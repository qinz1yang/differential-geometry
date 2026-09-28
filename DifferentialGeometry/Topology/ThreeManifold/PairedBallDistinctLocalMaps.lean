import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Locality
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SurvivingChartPreimages
import DifferentialGeometry.Topology.ThreeManifold.PairedBallPuncturedAtlas
import DifferentialGeometry.Topology.ThreeManifold.PairedBallMerge
import DifferentialGeometry.Topology.ThreeManifold.PairedBallSeam
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Interior
import DifferentialGeometry.Topology.Manifold.Diffeomorph.Sigma
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Maps

section

noncomputable section

open Set Metric Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.PairedBallGluing

universe u v w
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

variable {V : Type v} {E : Type w}
  (N : V → ConnectedClosedOrientedManifold.{u} 3)
  (endpoint : E → Bool → V)
  (chart : (e : E) → (b : Bool) →
    OrientedBallChart (N (endpoint e b)).toClosedOrientedManifold)
  (hdisj : Pairwise fun p q =>
    Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
      (flagMap N endpoint chart q '' closedBall (0 : E3) 2))
  (s : E) (a : BoundaryAttachment) (hends : endpoint s false ≠ endpoint s true)

private abbrev LFlag := {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s false}
private abbrev RFlag := {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s true}
private abbrev CS := (smoothConnectedSum (N (endpoint s false)) (N (endpoint s true))
  (chart s false) (chart s true) a).toConnectedClosedOrientedManifold

variable (b : LFlag endpoint s ⊕ RFlag endpoint s → OrientedBallChart (CS N endpoint chart s a).toClosedOrientedManifold)
  (C : SmoothBoundaryAtlas (𝓡 3) 3
    {x : (N (endpoint s false)).Carrier | (⟨endpoint s false, x⟩ : Σ v, (N v).Carrier) ∉
      ⋃ p, flagMap N endpoint chart p '' ball (0 : E3) 1})
  (D : SmoothBoundaryAtlas (𝓡 3) 3 (⋃ p, (b p).chart '' ball (0 : E3) 1)ᶜ)

include hdisj in
theorem isLocalDiffeomorphAt_core_left
    (hbL : ∀ p x, x ∈ closedBall (0 : E3) 2 →
      ∃ hx : (remainingIncidenceChart N endpoint chart s (endpoint s false) p).chart x ∉
          (chart s false).chart '' ball (0 : E3) 1,
        (b (Sum.inl p)).chart x = ConnectedSumQuotient.inl (chart s false).toBallChart
          (chart s true).toBallChart a.1.toHomeomorph
          ⟨(remainingIncidenceChart N endpoint chart s (endpoint s false) p).chart x, hx⟩)
    (hbR : ∀ p x, x ∈ closedBall (0 : E3) 2 →
      ∃ hx : (remainingIncidenceChart N endpoint chart s (endpoint s true) p).chart x ∉
          (chart s true).chart '' ball (0 : E3) 1,
        (b (Sum.inr p)).chart x = ConnectedSumQuotient.inr (chart s false).toBallChart
          (chart s true).toBallChart a.1.toHomeomorph
          ⟨(remainingIncidenceChart N endpoint chart s (endpoint s true) p).chart x, hx⟩)
    (F : PuncturedFactor N endpoint chart (endpoint s false) →
      ↥((⋃ p, (b p).chart '' ball (0 : E3) 1)ᶜ))
    (hF : ∀ x, (F x).val = ConnectedSumQuotient.inl (chart s false).toBallChart
      (chart s true).toBallChart a.1.toHomeomorph
      (selectedPuncturedFactorHomeomorph N endpoint chart s false hends x).val)
    (x : PuncturedFactor N endpoint chart (endpoint s false))
    (hx : x.val ∉ (chart s false).chart '' closedBall (0 : E3) 1) :
    let _ : ChartedSpace (EuclideanHalfSpace 3) (PuncturedFactor N endpoint chart (endpoint s false)) := C.toChartedSpace
    let _ := D.toChartedSpace
    IsLocalDiffeomorphAt (𝓡∂ 3) (𝓡∂ 3) ∞ F x := by
  let _ : ChartedSpace (EuclideanHalfSpace 3) (PuncturedFactor N endpoint chart (endpoint s false)) := C.toChartedSpace
  let _ := D.toChartedSpace
  let U := (chart s false).toBallChart.interior
  let g : U → (CS N endpoint chart s a).Carrier := ConnectedSumQuotient.interiorLeft (chart s false).toBallChart (chart s true).toBallChart a.1
  have hg : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ g :=
    (smoothConnectedSum (N (endpoint s false)) (N (endpoint s true))
      (chart s false) (chart s true) a).interiorLeft_localDiffeomorph
  apply C.isLocalDiffeomorphAt_of_open_ambient_map D U g hg _ F _ x hx
  · intro y
    have hn : y.val ∉ (chart s false).chart '' ball (0 : E3) 1 :=
      fun h => y.property (Set.image_mono ball_subset_closedBall h)
    have hsrc : (⟨endpoint s false, y.val⟩ : Σ v, (N v).Carrier) ∉
        ⋃ p, flagMap N endpoint chart p '' ball (0 : E3) 1 ↔
        y.val ∉ ⋃ p, (remainingIncidenceChart N endpoint chart s (endpoint s false) p).chart ''
          ball (0 : E3) 1 := by
      rw [selected_holes_iff N endpoint chart s false hends]
      simp only [hn, false_or]
    have ht := ConnectedSumQuotient.inl_mem_surviving_image_iff_of_avoids_boundary
      (chart s false) (chart s true) a
      (remainingIncidenceChart N endpoint chart s (endpoint s false))
      (remainingIncidenceChart N endpoint chart s (endpoint s true)) b hbL hbR
      (remainingIncidenceChart_avoids_selected N endpoint chart s true hdisj)
      (ball (0 : E3) 1)
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num)))
      ((chart s false).toBallChart.interiorToPunctured y)
    exact hsrc.trans (not_congr ht).symm
  · intro y hy
    exact hF y

end DifferentialGeometry.Topology.PairedBallGluing

end

end

section

noncomputable section

open Set Metric Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.PairedBallGluing

universe u v w

variable {V : Type v} {E : Type w}
  (N : V → ConnectedClosedOrientedManifold.{u} 3)
  (endpoint : E → Bool → V)
  (chart : (e : E) → (b : Bool) →
    OrientedBallChart (N (endpoint e b)).toClosedOrientedManifold)
  (hdisj : Pairwise fun p q =>
    Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
      (flagMap N endpoint chart q '' closedBall (0 : E3) 2))
  (s : E) (a : BoundaryAttachment) (hends : endpoint s false ≠ endpoint s true)


variable (b : LFlag endpoint s ⊕ RFlag endpoint s → OrientedBallChart (CS N endpoint chart s a).toClosedOrientedManifold)
  (C : SmoothBoundaryAtlas (𝓡 3) 3
    {x : (N (endpoint s true)).Carrier | (⟨endpoint s true, x⟩ : Σ v, (N v).Carrier) ∉
      ⋃ p, flagMap N endpoint chart p '' ball (0 : E3) 1})
  (D : SmoothBoundaryAtlas (𝓡 3) 3 (⋃ p, (b p).chart '' ball (0 : E3) 1)ᶜ)

include hdisj in
theorem isLocalDiffeomorphAt_core_right
    (hbL : ∀ p x, x ∈ closedBall (0 : E3) 2 →
      ∃ hx : (remainingIncidenceChart N endpoint chart s (endpoint s false) p).chart x ∉
          (chart s false).chart '' ball (0 : E3) 1,
        (b (Sum.inl p)).chart x = ConnectedSumQuotient.inl (chart s false).toBallChart
          (chart s true).toBallChart a.1.toHomeomorph
          ⟨(remainingIncidenceChart N endpoint chart s (endpoint s false) p).chart x, hx⟩)
    (hbR : ∀ p x, x ∈ closedBall (0 : E3) 2 →
      ∃ hx : (remainingIncidenceChart N endpoint chart s (endpoint s true) p).chart x ∉
          (chart s true).chart '' ball (0 : E3) 1,
        (b (Sum.inr p)).chart x = ConnectedSumQuotient.inr (chart s false).toBallChart
          (chart s true).toBallChart a.1.toHomeomorph
          ⟨(remainingIncidenceChart N endpoint chart s (endpoint s true) p).chart x, hx⟩)
    (F : PuncturedFactor N endpoint chart (endpoint s true) →
      ↥((⋃ p, (b p).chart '' ball (0 : E3) 1)ᶜ))
    (hF : ∀ x, (F x).val = ConnectedSumQuotient.inr (chart s false).toBallChart
      (chart s true).toBallChart a.1.toHomeomorph
      (selectedPuncturedFactorHomeomorph N endpoint chart s true hends x).val)
    (x : PuncturedFactor N endpoint chart (endpoint s true))
    (hx : x.val ∉ (chart s true).chart '' closedBall (0 : E3) 1) :
    let _ : ChartedSpace (EuclideanHalfSpace 3) (PuncturedFactor N endpoint chart (endpoint s true)) := C.toChartedSpace
    let _ := D.toChartedSpace
    IsLocalDiffeomorphAt (𝓡∂ 3) (𝓡∂ 3) ∞ F x := by
  let _ : ChartedSpace (EuclideanHalfSpace 3) (PuncturedFactor N endpoint chart (endpoint s true)) := C.toChartedSpace
  let _ := D.toChartedSpace
  let U := (chart s true).toBallChart.interior
  let g : U → (CS N endpoint chart s a).Carrier := ConnectedSumQuotient.interiorRight (chart s false).toBallChart (chart s true).toBallChart a.1
  have hg : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ g :=
    (smoothConnectedSum (N (endpoint s false)) (N (endpoint s true))
      (chart s false) (chart s true) a).interiorRight_localDiffeomorph
  apply C.isLocalDiffeomorphAt_of_open_ambient_map D U g hg _ F _ x hx
  · intro y
    have hn : y.val ∉ (chart s true).chart '' ball (0 : E3) 1 :=
      fun h => y.property (Set.image_mono ball_subset_closedBall h)
    have hsrc : (⟨endpoint s true, y.val⟩ : Σ v, (N v).Carrier) ∉
        ⋃ p, flagMap N endpoint chart p '' ball (0 : E3) 1 ↔
        y.val ∉ ⋃ p, (remainingIncidenceChart N endpoint chart s (endpoint s true) p).chart ''
          ball (0 : E3) 1 := by
      rw [selected_holes_iff N endpoint chart s true hends]
      simp only [hn, false_or]
    have ht := ConnectedSumQuotient.inr_mem_surviving_image_iff_of_avoids_boundary
      (chart s false) (chart s true) a
      (remainingIncidenceChart N endpoint chart s (endpoint s false))
      (remainingIncidenceChart N endpoint chart s (endpoint s true)) b hbL hbR
      (remainingIncidenceChart_avoids_selected N endpoint chart s false hdisj)
      (ball (0 : E3) 1)
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num)))
      ((chart s true).toBallChart.interiorToPunctured y)
    exact hsrc.trans (not_congr ht).symm
  · intro y hy
    exact hF y

end DifferentialGeometry.Topology.PairedBallGluing

end

end

section

noncomputable section

open Set Metric

namespace DifferentialGeometry.Topology.PairedBallGluing

universe u v w

variable {V : Type v} {E : Type w}
  (N : V → ConnectedClosedOrientedManifold.{u} 3)
  (endpoint : E → Bool → V)
  (chart : (e : E) → (b : Bool) →
    OrientedBallChart (N (endpoint e b)).toClosedOrientedManifold)
  (hdisj : Pairwise fun p q =>
    Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
      (flagMap N endpoint chart q '' closedBall (0 : E3) 2))
  (s : E) (a : BoundaryAttachment) (hends : endpoint s false ≠ endpoint s true)


variable (b : LFlag endpoint s ⊕ RFlag endpoint s → OrientedBallChart (CS N endpoint chart s a).toClosedOrientedManifold)
  {Z : Type*}
  (H : Quot (seamRel N endpoint chart hdisj s a) →
    ↥((⋃ p, (b p).chart '' ball (0 : E3) 1)ᶜ) ⊕ Z)
  (hL : ∀ x : PuncturedFactor N endpoint chart (endpoint s false),
    ∃ y, H (Quot.mk _ ⟨endpoint s false, x⟩) = Sum.inl y ∧
      y.val = ConnectedSumQuotient.inl (chart s false).toBallChart (chart s true).toBallChart
        a.1.toHomeomorph (selectedPuncturedFactorHomeomorph N endpoint chart s false hends x).val)

def leftFactorMap (x : PuncturedFactor N endpoint chart (endpoint s false)) :
    ↥((⋃ p, (b p).chart '' ball (0 : E3) 1)ᶜ) := (hL x).choose

theorem leftFactorMap_rep (x : PuncturedFactor N endpoint chart (endpoint s false)) :
    H (Quot.mk _ ⟨endpoint s false, x⟩) =
      Sum.inl (leftFactorMap N endpoint chart hdisj s a hends b H hL x) := (hL x).choose_spec.1

theorem leftFactorMap_val (x : PuncturedFactor N endpoint chart (endpoint s false)) :
    (leftFactorMap N endpoint chart hdisj s a hends b H hL x).val =
      ConnectedSumQuotient.inl (chart s false).toBallChart (chart s true).toBallChart
        a.1.toHomeomorph (selectedPuncturedFactorHomeomorph N endpoint chart s false hends x).val :=
  (hL x).choose_spec.2

variable (hR : ∀ x : PuncturedFactor N endpoint chart (endpoint s true),
    ∃ y, H (Quot.mk _ ⟨endpoint s true, x⟩) = Sum.inl y ∧
      y.val = ConnectedSumQuotient.inr (chart s false).toBallChart (chart s true).toBallChart
        a.1.toHomeomorph (selectedPuncturedFactorHomeomorph N endpoint chart s true hends x).val)

def rightFactorMap (x : PuncturedFactor N endpoint chart (endpoint s true)) :
    ↥((⋃ p, (b p).chart '' ball (0 : E3) 1)ᶜ) := (hR x).choose

theorem rightFactorMap_rep (x : PuncturedFactor N endpoint chart (endpoint s true)) :
    H (Quot.mk _ ⟨endpoint s true, x⟩) =
      Sum.inl (rightFactorMap N endpoint chart hdisj s a hends b H hR x) := (hR x).choose_spec.1

theorem rightFactorMap_val (x : PuncturedFactor N endpoint chart (endpoint s true)) :
    (rightFactorMap N endpoint chart hdisj s a hends b H hR x).val =
      ConnectedSumQuotient.inr (chart s false).toBallChart (chart s true).toBallChart
        a.1.toHomeomorph (selectedPuncturedFactorHomeomorph N endpoint chart s true hends x).val :=
  (hR x).choose_spec.2

end DifferentialGeometry.Topology.PairedBallGluing

end

end

section

noncomputable section

open Set Metric Function Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.PairedBallGluing

universe u v w
private abbrev IC := (𝓡 2).prod 𝓘(ℝ, ℝ)

private def seamDomainDiffeomorph :
    SelfAttachment.directSeamDomain ≃ₘ⟮IC, IC⟯ ConnectedSumQuotient.CollarDomain where
  toFun p := (p.val.1, ⟨p.val.2,p.property.2⟩)
  invFun p := ⟨(p.1,p.2.val),trivial,p.2.property⟩
  left_inv p := rfl
  right_inv p := rfl
  contMDiff_toFun := by
    apply ContMDiff.prodMk (contMDiff_fst.comp contMDiff_subtype_val)
    apply (ContMDiff.subtypeVal_comp_iff ConnectedSumQuotient.collarInterval _).mp
    exact contMDiff_snd.comp contMDiff_subtype_val
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff SelfAttachment.directSeamDomain _).mp
    exact contMDiff_fst.prodMk (contMDiff_subtype_val.comp contMDiff_snd)

variable {V : Type v} {E : Type w} [Finite E]
  (N : V → ConnectedClosedOrientedManifold.{u} 3)
  (endpoint : E → Bool → V)
  (chart : (e : E) → (b : Bool) →
    OrientedBallChart (N (endpoint e b)).toClosedOrientedManifold)
  (hdisj : Pairwise fun p q =>
    Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
      (flagMap N endpoint chart q '' closedBall (0 : E3) 2))
  (s : E) (a : BoundaryAttachment) (hends : endpoint s false ≠ endpoint s true)


variable (b : LFlag endpoint s ⊕ RFlag endpoint s → OrientedBallChart (CS N endpoint chart s a).toClosedOrientedManifold)
  (D : SmoothBoundaryAtlas (𝓡 3) 3 (⋃ p, (b p).chart '' ball (0 : E3) 1)ᶜ)
  {Z : Type*} [TopologicalSpace Z] [ChartedSpace (EuclideanHalfSpace 3) Z]
  [IsManifold (𝓡∂ 3) ∞ Z]
  (H : Quot (seamRel N endpoint chart hdisj s a) →
    ↥((⋃ p, (b p).chart '' ball (0 : E3) 1)ᶜ) ⊕ Z)
  (hL : ∀ x : PuncturedFactor N endpoint chart (endpoint s false),
    ∃ y, H (Quot.mk _ ⟨endpoint s false, x⟩) = Sum.inl y ∧
      y.val = ConnectedSumQuotient.inl (chart s false).toBallChart (chart s true).toBallChart
        a.1.toHomeomorph (selectedPuncturedFactorHomeomorph N endpoint chart s false hends x).val)
  (hR : ∀ x : PuncturedFactor N endpoint chart (endpoint s true),
    ∃ y, H (Quot.mk _ ⟨endpoint s true, x⟩) = Sum.inl y ∧
      y.val = ConnectedSumQuotient.inr (chart s false).toBallChart (chart s true).toBallChart
        a.1.toHomeomorph (selectedPuncturedFactorHomeomorph N endpoint chart s true hends x).val)

private def seamImage (p : SelfAttachment.directSeamDomain) :
    ↥((⋃ p, (b p).chart '' ball (0 : E3) 1)ᶜ) :=
  if ht : 0 ≤ p.val.2 then
    leftFactorMap N endpoint chart hdisj s a hends b H hL
      (radialPoint N endpoint chart hdisj s false p.val.1 (1 + p.val.2)
        ⟨by linarith,by linarith [p.property.2.2]⟩)
  else
    rightFactorMap N endpoint chart hdisj s a hends b H hR
      (radialPoint N endpoint chart hdisj s true (a.1 p.val.1) (1 - p.val.2)
        ⟨by linarith,by linarith [p.property.2.1]⟩)

omit [Finite E] [TopologicalSpace Z] [ChartedSpace (EuclideanHalfSpace 3) Z]
  [IsManifold (𝓡∂ 3) ∞ Z] in
private theorem seamImage_val (p : SelfAttachment.directSeamDomain) :
    (seamImage N endpoint chart hdisj s a hends b H hL hR p).val =
      ConnectedSumQuotient.collarMap (chart s false).toBallChart (chart s true).toBallChart a.1
        (seamDomainDiffeomorph p) := by
  have hleft : (seamDomainDiffeomorph p).1 = p.val.1 := rfl
  have hright : ((seamDomainDiffeomorph p).2 : ℝ) = p.val.2 := rfl
  by_cases ht : 0 ≤ p.val.2
  · rw [show seamImage N endpoint chart hdisj s a hends b H hL hR p =
        leftFactorMap N endpoint chart hdisj s a hends b H hL
          (radialPoint N endpoint chart hdisj s false p.val.1 (1 + p.val.2)
            ⟨by linarith,by linarith [p.property.2.2]⟩) from dite_eq_left ht]
    rw [leftFactorMap_val,ConnectedSumQuotient.collarMap_of_nonneg _ _ _ _ (by simpa only [hright] using ht)]
    congr 1
  · rw [show seamImage N endpoint chart hdisj s a hends b H hL hR p =
        rightFactorMap N endpoint chart hdisj s a hends b H hR
          (radialPoint N endpoint chart hdisj s true (a.1 p.val.1) (1 - p.val.2)
            ⟨by linarith,by linarith [p.property.2.1]⟩) from dite_eq_right ht]
    rw [rightFactorMap_val,ConnectedSumQuotient.collarMap_of_neg _ _ _ _
      (by simpa only [hright] using lt_of_not_ge ht)]
    congr 1

omit [Finite E] [TopologicalSpace Z] [ChartedSpace (EuclideanHalfSpace 3) Z]
  [IsManifold (𝓡∂ 3) ∞ Z] in
private theorem seamChart_comp_eq :
    H ∘ seamChart N endpoint chart hdisj s a =
      Sum.inl ∘ seamImage N endpoint chart hdisj s a hends b H hL hR := by
  funext p
  simp only [Function.comp_apply,seamChart,seamImage]
  split_ifs with ht
  · exact leftFactorMap_rep N endpoint chart hdisj s a hends b H hL _
  · exact rightFactorMap_rep N endpoint chart hdisj s a hends b H hR _

include hdisj hends hL hR in
theorem isLocalDiffeomorph_seam_comp_of_factor_representatives
    (hbL : ∀ p x, x ∈ closedBall (0 : E3) 2 →
      ∃ hx : (remainingIncidenceChart N endpoint chart s (endpoint s false) p).chart x ∉
          (chart s false).chart '' ball (0 : E3) 1,
        (b (Sum.inl p)).chart x = ConnectedSumQuotient.inl (chart s false).toBallChart
          (chart s true).toBallChart a.1.toHomeomorph
          ⟨(remainingIncidenceChart N endpoint chart s (endpoint s false) p).chart x, hx⟩)
    (hbR : ∀ p x, x ∈ closedBall (0 : E3) 2 →
      ∃ hx : (remainingIncidenceChart N endpoint chart s (endpoint s true) p).chart x ∉
          (chart s true).chart '' ball (0 : E3) 1,
        (b (Sum.inr p)).chart x = ConnectedSumQuotient.inr (chart s false).toBallChart
          (chart s true).toBallChart a.1.toHomeomorph
          ⟨(remainingIncidenceChart N endpoint chart s (endpoint s true) p).chart x, hx⟩) :
    let _ := D.toChartedSpace
    IsLocalDiffeomorph IC (𝓡∂ 3) ∞ (H ∘ seamChart N endpoint chart hdisj s a) := by
  let _ := D.toChartedSpace
  let _ := D.isManifold
  rw [seamChart_comp_eq N endpoint chart hdisj s a hends b H hL hR]
  apply DifferentialGeometry.isLocalDiffeomorph_comp isLocalDiffeomorph_sum_inl
  intro p
  apply D.isLocalDiffeomorphAt_of_subtype_val
  · rw [seamImage_val]
    have hsep (side : Bool) : ∀ q : {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s side},
        Disjoint ((remainingIncidenceChart N endpoint chart s (endpoint s side) q).chart '' closedBall (0 : E3) 2)
          ((chart s side).chart '' closedBall (0 : E3) 2) := by
      intro q
      rw [disjoint_left]
      rintro x ⟨y,hy,hyx⟩ ⟨z,hz,hzx⟩
      apply disjoint_left.mp (hdisj (show q.val ≠ (s, side) from
        fun h => q.property.1 (congrArg Prod.fst h)))
        (⟨y,hy,rfl⟩ : flagMap N endpoint chart q.val y ∈ flagMap N endpoint chart q.val '' closedBall (0 : E3) 2)
      refine ⟨z,hz,?_⟩
      rw [← remainingIncidenceChart_sigma_apply N endpoint chart s (endpoint s side) q,hyx]
      exact congrArg (Sigma.mk (endpoint s side)) hzx
    exact ConnectedSumQuotient.collarMap_mem_interior_surviving_complement
      (chart s false) (chart s true) a
      (remainingIncidenceChart N endpoint chart s (endpoint s false))
      (remainingIncidenceChart N endpoint chart s (endpoint s true)) b hbL hbR
      (hsep false) (hsep true) _
  · have heq : (Subtype.val ∘ seamImage N endpoint chart hdisj s a hends b H hL hR) =
        ConnectedSumQuotient.collarMap (chart s false).toBallChart (chart s true).toBallChart a.1 ∘
          seamDomainDiffeomorph := funext (seamImage_val N endpoint chart hdisj s a hends b H hL hR)
    rw [heq]
    exact (seamDomainDiffeomorph.isLocalDiffeomorph p).comp (𝓡 3) _
      ((smoothConnectedSum (N (endpoint s false)) (N (endpoint s true))
        (chart s false) (chart s true) a).collar_localDiffeomorph _)

end DifferentialGeometry.Topology.PairedBallGluing

end

end

section

noncomputable section

open Set Metric Function Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.PairedBallGluing

universe u v w

variable {V : Type v} {E : Type w}
  (N : V → ConnectedClosedOrientedManifold.{u} 3)
  (endpoint : E → Bool → V)
  (chart : (e : E) → (b : Bool) →
    OrientedBallChart (N (endpoint e b)).toClosedOrientedManifold)
  (hdisj : Pairwise fun p q =>
    Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
      (flagMap N endpoint chart q '' closedBall (0 : E3) 2))
  (s : E) (a : BoundaryAttachment) (hends : endpoint s false ≠ endpoint s true)

private abbrev Rest := {v // v ≠ endpoint s false ∧ v ≠ endpoint s true}

variable (b : LFlag endpoint s ⊕ RFlag endpoint s → OrientedBallChart (CS N endpoint chart s a).toClosedOrientedManifold)
  (C : ∀ v, SmoothBoundaryAtlas (𝓡 3) 3
    {x : (N v).Carrier | (⟨v, x⟩ : Σ v, (N v).Carrier) ∉
      ⋃ p, flagMap N endpoint chart p '' ball (0 : E3) 1})
  (D : SmoothBoundaryAtlas (𝓡 3) 3 (⋃ p, (b p).chart '' ball (0 : E3) 1)ᶜ)
  (H : Quot (seamRel N endpoint chart hdisj s a) →
    ↥((⋃ p, (b p).chart '' ball (0 : E3) 1)ᶜ) ⊕
      (Σ v : Rest endpoint s, PuncturedFactor N endpoint chart v.val))
  (hL : ∀ x : PuncturedFactor N endpoint chart (endpoint s false),
    ∃ y, H (Quot.mk _ ⟨endpoint s false, x⟩) = Sum.inl y ∧
      y.val = ConnectedSumQuotient.inl (chart s false).toBallChart (chart s true).toBallChart
        a.1.toHomeomorph (selectedPuncturedFactorHomeomorph N endpoint chart s false hends x).val)
  (hR : ∀ x : PuncturedFactor N endpoint chart (endpoint s true),
    ∃ y, H (Quot.mk _ ⟨endpoint s true, x⟩) = Sum.inl y ∧
      y.val = ConnectedSumQuotient.inr (chart s false).toBallChart (chart s true).toBallChart
        a.1.toHomeomorph (selectedPuncturedFactorHomeomorph N endpoint chart s true hends x).val)
  (hu : ∀ (v : Rest endpoint s) (x : PuncturedFactor N endpoint chart v.val),
    H (Quot.mk _ ⟨v.val, x⟩) = Sum.inr ⟨v, x⟩)

include hdisj hends hL hR hu in
theorem isLocalDiffeomorph_core_comp_of_factor_representatives
    (hbL : ∀ p x, x ∈ closedBall (0 : E3) 2 →
      ∃ hx : (remainingIncidenceChart N endpoint chart s (endpoint s false) p).chart x ∉
          (chart s false).chart '' ball (0 : E3) 1,
        (b (Sum.inl p)).chart x = ConnectedSumQuotient.inl (chart s false).toBallChart
          (chart s true).toBallChart a.1.toHomeomorph
          ⟨(remainingIncidenceChart N endpoint chart s (endpoint s false) p).chart x, hx⟩)
    (hbR : ∀ p x, x ∈ closedBall (0 : E3) 2 →
      ∃ hx : (remainingIncidenceChart N endpoint chart s (endpoint s true) p).chart x ∉
          (chart s true).chart '' ball (0 : E3) 1,
        (b (Sum.inr p)).chart x = ConnectedSumQuotient.inr (chart s false).toBallChart
          (chart s true).toBallChart a.1.toHomeomorph
          ⟨(remainingIncidenceChart N endpoint chart s (endpoint s true) p).chart x, hx⟩) :
    let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3) (PuncturedFactor N endpoint chart v) :=
      fun v => (C v).toChartedSpace
    let _ := D.toChartedSpace
    IsLocalDiffeomorph (𝓡∂ 3) (𝓡∂ 3) ∞
      (H ∘ seamCoreInclusion N endpoint chart hdisj s a) := by
  let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3) (PuncturedFactor N endpoint chart v) :=
    fun v => (C v).toChartedSpace
  let _ : ∀ v, IsManifold (𝓡∂ 3) ∞ (PuncturedFactor N endpoint chart v) := fun v => (C v).isManifold
  let _ := D.toChartedSpace
  let _ := D.isManifold
  dsimp only
  let Q := Σ v, PuncturedFactor N endpoint chart v
  let O := seamCore N endpoint chart hdisj s
  let G := H ∘ seamCoreInclusion N endpoint chart hdisj s a
  intro x
  obtain ⟨⟨v,y⟩,hx⟩ := x
  let U : TopologicalSpace.Opens (PuncturedFactor N endpoint chart v) :=
    ⟨(Sigma.mk v) ⁻¹' O, O.isOpen.preimage continuous_sigmaMk⟩
  let lift : U → O := fun z => ⟨⟨v,z.val⟩,z.property⟩
  let yU : U := ⟨y,hx⟩
  have hlift : IsLocalDiffeomorph (𝓡∂ 3) (𝓡∂ 3) ∞ lift := by
    intro z
    apply DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict
      (V := O) (f := fun z : U => (⟨v,z.val⟩ : Q))
      (fun z : U => z.property)
    exact (DifferentialGeometry.isLocalDiffeomorph_subtype_val U z).comp (𝓡∂ 3) Q
      (isLocalDiffeomorph_sigmaMk (I := 𝓡∂ 3) (M := PuncturedFactor N endpoint chart) v z.val)
  apply DifferentialGeometry.isLocalDiffeomorphAt_of_comp (f := lift) (g := G) (x := yU) _ (hlift yU)
  by_cases hv : v = endpoint s false
  · subst v
    have havoid : y.val ∉ (chart s false).chart '' closedBall (0 : E3) 1 := by
      intro hy
      apply (mem_seamCore_iff N endpoint chart hdisj s ⟨endpoint s false,y⟩).mp hx
      exact Or.inl (by rcases hy with ⟨z,hz,hzy⟩; exact ⟨z,hz,congrArg (Sigma.mk _) hzy⟩)
    let F := leftFactorMap N endpoint chart hdisj s a hends b H hL
    have hF := isLocalDiffeomorphAt_core_left N endpoint chart hdisj s a hends b
      (C (endpoint s false)) D hbL hbR F
      (leftFactorMap_val N endpoint chart hdisj s a hends b H hL) y havoid
    have hcomp := (DifferentialGeometry.isLocalDiffeomorph_subtype_val U yU).comp
      (𝓡∂ 3) _ hF
    have hsum := hcomp.comp (𝓡∂ 3) _ (isLocalDiffeomorph_sum_inl (I := 𝓡∂ 3)
      (N := Σ v : Rest endpoint s, PuncturedFactor N endpoint chart v.val) (F y))
    have heq : G ∘ lift = Sum.inl ∘ F ∘ (Subtype.val : U → _) := by
      funext z
      exact leftFactorMap_rep N endpoint chart hdisj s a hends b H hL z.val
    simpa only [heq] using hsum
  · by_cases hv' : v = endpoint s true
    · subst v
      have havoid : y.val ∉ (chart s true).chart '' closedBall (0 : E3) 1 := by
        intro hy
        apply (mem_seamCore_iff N endpoint chart hdisj s ⟨endpoint s true,y⟩).mp hx
        exact Or.inr (by rcases hy with ⟨z,hz,hzy⟩; exact ⟨z,hz,congrArg (Sigma.mk _) hzy⟩)
      let F := rightFactorMap N endpoint chart hdisj s a hends b H hR
      have hF := isLocalDiffeomorphAt_core_right N endpoint chart hdisj s a hends b
        (C (endpoint s true)) D hbL hbR F
        (rightFactorMap_val N endpoint chart hdisj s a hends b H hR) y havoid
      have hcomp := (DifferentialGeometry.isLocalDiffeomorph_subtype_val U yU).comp
        (𝓡∂ 3) _ hF
      have hsum := hcomp.comp (𝓡∂ 3) _ (isLocalDiffeomorph_sum_inl (I := 𝓡∂ 3)
        (N := Σ v : Rest endpoint s, PuncturedFactor N endpoint chart v.val) (F y))
      have heq : G ∘ lift = Sum.inl ∘ F ∘ (Subtype.val : U → _) := by
        funext z
        exact rightFactorMap_rep N endpoint chart hdisj s a hends b H hR z.val
      simpa only [heq] using hsum
    · let vr : Rest endpoint s := ⟨v,hv,hv'⟩
      have hcomp := (DifferentialGeometry.isLocalDiffeomorph_subtype_val U yU).comp (𝓡∂ 3) _
        (isLocalDiffeomorph_sigmaMk (I := 𝓡∂ 3)
          (M := fun v : Rest endpoint s => PuncturedFactor N endpoint chart v.val) vr y)
      have hsum := hcomp.comp (𝓡∂ 3) _ (isLocalDiffeomorph_sum_inr (I := 𝓡∂ 3)
        (M := Σ v : Rest endpoint s, PuncturedFactor N endpoint chart v.val)
        (N := ↥((⋃ p, (b p).chart '' ball (0 : E3) 1)ᶜ)) ⟨vr,y⟩)
      have heq : G ∘ lift = Sum.inr ∘ Sigma.mk vr ∘ (Subtype.val : U → _) := by
        funext z
        exact hu vr z.val
      simpa only [heq] using hsum

end DifferentialGeometry.Topology.PairedBallGluing

end

end

section

set_option autoImplicit false
noncomputable section
open Set Function Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.PairedBallGluing

universe u v w
variable {V : Type v} {E : Type w}
  (N : V → ConnectedClosedOrientedManifold.{u} 3)
  (endpoint : E → Bool → V)
  (chart : (e : E) → (b : Bool) →
    OrientedBallChart (N (endpoint e b)).toClosedOrientedManifold)
  (s : E) (a : BoundaryAttachment) (hends : endpoint s false ≠ endpoint s true)
  (b : ({p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s false} ⊕
      {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s true}) →
    OrientedBallChart (mergeFactor N endpoint chart s a none).toClosedOrientedManifold)
  (C : ∀ v, SmoothBoundaryAtlas (𝓡 3) 3
    {x : (N v).Carrier | (⟨v, x⟩ : Σ v, (N v).Carrier) ∉ ⋃ p, flagMap N endpoint chart p '' ball (0 : E3) 1})
  (D : SmoothBoundaryAtlas (𝓡 3) 3
    {y : (mergeFactor N endpoint chart s a none).Carrier | y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1})
  (C' : ∀ v, SmoothBoundaryAtlas (𝓡 3) 3
    {x : (mergeFactor N endpoint chart s a v).Carrier |
      (⟨v, x⟩ : Σ v, (mergeFactor N endpoint chart s a v).Carrier) ∉
        ⋃ p, flagMap (mergeFactor N endpoint chart s a)
          (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
          (fun e t => (mergeFlag N endpoint chart s a b e t).snd) p '' ball (0 : E3) 1})

theorem mergePuncturedFactorHomeomorph_isLocalDiffeomorph :
    let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3) (PuncturedFactor N endpoint chart v) := fun v => (C v).toChartedSpace
    let _ : ChartedSpace (EuclideanHalfSpace 3) {y : (mergeFactor N endpoint chart s a none).Carrier // y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1} := D.toChartedSpace
    let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3)
      (PuncturedFactor (mergeFactor N endpoint chart s a)
        (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
        (fun e t => (mergeFlag N endpoint chart s a b e t).snd) v) := fun v => (C' v).toChartedSpace
    IsLocalDiffeomorph (𝓡∂ 3) (𝓡∂ 3) ∞ (mergePuncturedFactorHomeomorph N endpoint chart s a b hends) := by
  let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3) (PuncturedFactor N endpoint chart v) := fun v => (C v).toChartedSpace
  let _ : ∀ v, IsManifold (𝓡∂ 3) ∞ (PuncturedFactor N endpoint chart v) := fun v => (C v).isManifold
  let _ : ChartedSpace (EuclideanHalfSpace 3) {y : (mergeFactor N endpoint chart s a none).Carrier // y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1} := D.toChartedSpace
  let _ : IsManifold (𝓡∂ 3) ∞ {y : (mergeFactor N endpoint chart s a none).Carrier // y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1} := D.isManifold
  let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3)
    (PuncturedFactor (mergeFactor N endpoint chart s a)
      (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
      (fun e t => (mergeFlag N endpoint chart s a b e t).snd) v) := fun v => (C' v).toChartedSpace
  let _ : ∀ v, IsManifold (𝓡∂ 3) ∞
    (PuncturedFactor (mergeFactor N endpoint chart s a)
      (fun e t => (mergeFlag N endpoint chart s a b e t).fst)
      (fun e t => (mergeFlag N endpoint chart s a b e t).snd) v) := fun v => (C' v).isManifold
  dsimp only
  apply (isLocalDiffeomorph_sigma_iff _).mpr
  intro v
  cases v with
  | none =>
    let _ := (C' none).toChartedSpace
    let _ := (C' none).isManifold
    let _ := D.toChartedSpace
    let _ := D.isManifold
    let T := (C' none).diffeomorphOfAmbient D (Diffeomorph.refl (𝓡 3) _ ∞)
      (fun x => not_congr (Set.ext_iff.mp (mergeFlag_holes_none N endpoint chart s a b hends (ball 0 1)) x))
    have heq : mergePuncturedFactorHomeomorph N endpoint chart s a b hends ∘ Sigma.mk none =
        Sum.inl ∘ T := by funext x; rfl
    rw [heq]
    exact DifferentialGeometry.isLocalDiffeomorph_comp isLocalDiffeomorph_sum_inl T.isLocalDiffeomorph
  | some v =>
    let _ := (C' (some v)).toChartedSpace
    let _ := (C' (some v)).isManifold
    let _ := (C v.val).toChartedSpace
    let _ := (C v.val).isManifold
    let T := (C' (some v)).diffeomorphOfAmbient (C v.val) (Diffeomorph.refl (𝓡 3) _ ∞)
      (fun x => not_congr (Set.ext_iff.mp (mergeFlag_holes_some N endpoint chart s a b v (ball 0 1)) x))
    have heq : mergePuncturedFactorHomeomorph N endpoint chart s a b hends ∘ Sigma.mk (some v) =
        Sum.inr ∘ (Sigma.mk v ∘ T) := by funext x; rfl
    rw [heq]
    exact DifferentialGeometry.isLocalDiffeomorph_comp isLocalDiffeomorph_sum_inr
      (DifferentialGeometry.isLocalDiffeomorph_comp (isLocalDiffeomorph_sigmaMk v) T.isLocalDiffeomorph)

end DifferentialGeometry.Topology.PairedBallGluing

end

end
