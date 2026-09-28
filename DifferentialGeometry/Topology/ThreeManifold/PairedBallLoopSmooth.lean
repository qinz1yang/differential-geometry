import DifferentialGeometry.Topology.ThreeManifold.PairedBallSeam
import DifferentialGeometry.Topology.ThreeManifold.PairedBallLoop
import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.ComplementSmooth
import DifferentialGeometry.Topology.Manifold.Diffeomorph.Sigma

set_option autoImplicit false
noncomputable section
open Set Function Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.PairedBallGluing

universe u v w
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
variable {V : Type v} {E : Type w}
  (N : V → ConnectedClosedOrientedManifold.{u} 3)
  (endpoint : E → Bool → V)
  (chart : (e : E) → (b : Bool) →
    OrientedBallChart (N (endpoint e b)).toClosedOrientedManifold)
  (s : E) (hloop : endpoint s true = endpoint s false)
  (hdisj : Pairwise fun p q =>
    Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
      (flagMap N endpoint chart q '' closedBall (0 : E3) 2))

include hloop in
private theorem selected_mem_coreInterior (x : PuncturedFactor N endpoint chart (endpoint s false))
    (hx : (⟨endpoint s false, x⟩ : Σ v, PuncturedFactor N endpoint chart v) ∈ seamCore N endpoint chart hdisj s) :
    x.val ∈ SelfAttachment.coreInterior (chart s false).toBallChart
      (loopSecondChart N endpoint chart s hloop).toBallChart := by
  have h := (mem_seamCore_iff N endpoint chart hdisj s _).mp hx
  rintro (⟨y, hy, hyx⟩ | ⟨y, hy, hyx⟩)
  · exact h (Or.inl ⟨y, hy, congrArg (Sigma.mk (endpoint s false)) hyx⟩)
  · refine h (Or.inr ⟨y, hy, ?_⟩)
    exact (incidenceChart_sigma_apply N endpoint chart (endpoint s false) ⟨(s, true), hloop⟩ y).symm.trans
      (congrArg (Sigma.mk (endpoint s false)) hyx)

variable (a : BoundaryAttachment)
  (S : SmoothSelfAttachment (chart s false) (loopSecondChart N endpoint chart s hloop)
    (disjoint_loop_charts N endpoint chart s hloop hdisj) a)
  {Z : ClosedOrientedManifold.{u} 3}
  (F : ClosedOrientedManifold.OrientedDiffeomorph S.toConnectedClosedOrientedManifold.toClosedOrientedManifold Z)
  (b : {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s false} → OrientedBallChart Z)
  (hb : ∀ i x, x ∈ closedBall (0 : E3) 2 →
    ∃ hx : (remainingIncidenceChart N endpoint chart s (endpoint s false) i).chart x ∈
      ((chart s false).chart '' ball 0 1 ∪ (loopSecondChart N endpoint chart s hloop).chart '' ball 0 1)ᶜ,
      (b i).chart x = F.val (SelfAttachment.coreInclusion (chart s false).toBallChart
        (loopSecondChart N endpoint chart s hloop).toBallChart
        (disjoint_loop_charts N endpoint chart s hloop hdisj) a.val.toHomeomorph
        ⟨(remainingIncidenceChart N endpoint chart s (endpoint s false) i).chart x, hx⟩))
  (C : ∀ v, SmoothBoundaryAtlas (𝓡 3) 3
    {x : (N v).Carrier | (⟨v, x⟩ : Σ v, (N v).Carrier) ∉ ⋃ p, flagMap N endpoint chart p '' ball (0 : E3) 1})
  (D : SmoothBoundaryAtlas (𝓡 3) 3 {y : Z.Carrier | y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1})
  (H : Quot (seamRel N endpoint chart hdisj s a) →
    {y : Z.Carrier // y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1} ⊕
      (Σ v : {v // v ≠ endpoint s false}, PuncturedFactor N endpoint chart v.val))
  (hH : ∀ x : PuncturedFactor N endpoint chart (endpoint s false),
    ∃ y, H (Quot.mk _ ⟨endpoint s false, x⟩) = Sum.inl y ∧
      y.val = F.val (SelfAttachment.coreToBand (chart s false).toBallChart
        (loopSecondChart N endpoint chart s hloop).toBallChart
        (disjoint_loop_charts N endpoint chart s hloop hdisj) a.val.toHomeomorph
        (loopPuncturedFactorHomeomorph N endpoint chart s hloop x).val))
  (hR : ∀ (v : {v // v ≠ endpoint s false}) (x : PuncturedFactor N endpoint chart v.val),
    H (Quot.mk _ ⟨v.val, x⟩) = Sum.inr ⟨v, x⟩)

include hb hH hR in
theorem loop_seamCore_isLocalDiffeomorph :
    let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3) (PuncturedFactor N endpoint chart v) := fun v => (C v).toChartedSpace
    let _ : ChartedSpace (EuclideanHalfSpace 3) {y : Z.Carrier // y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1} := D.toChartedSpace
    IsLocalDiffeomorph (𝓡∂ 3) (𝓡∂ 3) ∞ (H ∘ seamCoreInclusion N endpoint chart hdisj s a) := by
  let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3) (PuncturedFactor N endpoint chart v) := fun v => (C v).toChartedSpace
  let _ : ∀ v, IsManifold (𝓡∂ 3) ∞ (PuncturedFactor N endpoint chart v) := fun v => (C v).isManifold
  let _ : ChartedSpace (EuclideanHalfSpace 3) {y : Z.Carrier // y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1} := D.toChartedSpace
  let _ : IsManifold (𝓡∂ 3) ∞ {y : Z.Carrier // y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1} := D.isManifold
  dsimp only
  let f := H ∘ Quot.mk (seamRel N endpoint chart hdisj s a)
  have hf : IsLocalDiffeomorphOn (𝓡∂ 3) (𝓡∂ 3) ∞ f (seamCore N endpoint chart hdisj s) := by
    rintro ⟨⟨v, x⟩, hx⟩
    by_cases hv : v = endpoint s false
    · subst v
      let _ := (C (endpoint s false)).toChartedSpace
      let _ := (C (endpoint s false)).isManifold
      let _ := D.toChartedSpace
      let _ := D.isManifold
      let L : PuncturedFactor N endpoint chart (endpoint s false) →
          {y : Z.Carrier // y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1} := fun y => Classical.choose (hH y)
      have hLval (y) : ∃ hy, (L y).val = F.val (SelfAttachment.coreToBand (chart s false).toBallChart
          (loopSecondChart N endpoint chart s hloop).toBallChart
          (disjoint_loop_charts N endpoint chart s hloop hdisj) a.val.toHomeomorph ⟨y.val, hy⟩) :=
        ⟨(loopPuncturedFactorHomeomorph N endpoint chart s hloop y).val.property,
          (Classical.choose_spec (hH y)).2⟩
      have hK (y : (N (endpoint s false)).Carrier) :
          (⟨endpoint s false, y⟩ : Σ v, (N v).Carrier) ∉ ⋃ p, flagMap N endpoint chart p '' ball (0 : E3) 1 ↔
          y ∉ ((chart s false).chart '' ball 0 1 ∪ (loopSecondChart N endpoint chart s hloop).chart '' ball 0 1) ∪
            ⋃ i, (remainingIncidenceChart N endpoint chart s (endpoint s false) i).chart '' ball (0 : E3) 1 :=
        not_congr (loop_holes_iff N endpoint chart s hloop y)
      have hL := S.coreToBand_complement_isLocalDiffeomorphAt F
        (remainingIncidenceChart N endpoint chart s (endpoint s false)) b
        (fun i y hy => remainingIncidenceChart_avoids_incidence N endpoint chart s hdisj (endpoint s false) i false rfl y hy)
        (fun i y hy => remainingIncidenceChart_avoids_incidence N endpoint chart s hdisj (endpoint s false) i true hloop y hy)
        hb hK (C (endpoint s false)) D L hLval x
        (selected_mem_coreInterior N endpoint chart s hloop hdisj x hx)
      have heq : f ∘ Sigma.mk (endpoint s false) = Sum.inl ∘ L := by
        funext y
        exact (Classical.choose_spec (hH y)).1
      have hL' : IsLocalDiffeomorphAt (𝓡∂ 3) (𝓡∂ 3) ∞ L x := hL
      have hcomp := hL'.comp (𝓡∂ 3) _ (isLocalDiffeomorph_sum_inl (I := 𝓡∂ 3)
        (N := Σ v : {v // v ≠ endpoint s false}, PuncturedFactor N endpoint chart v.val) (L x))
      exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp (f := Sigma.mk (endpoint s false)) (x := x)
        (heq.symm ▸ hcomp) (isLocalDiffeomorph_sigmaMk (I := 𝓡∂ 3) (endpoint s false) x)
    · have heq : f ∘ Sigma.mk v = Sum.inr ∘ (fun y => (⟨⟨v, hv⟩, y⟩ :
          Σ w : {w // w ≠ endpoint s false}, PuncturedFactor N endpoint chart w.val)) := by
        funext y
        exact hR ⟨v, hv⟩ y
      have hcomp := (isLocalDiffeomorph_sigmaMk (I := 𝓡∂ 3)
        (M := fun w : {w // w ≠ endpoint s false} => PuncturedFactor N endpoint chart w.val) ⟨v, hv⟩ x).comp
        (𝓡∂ 3) _ (isLocalDiffeomorph_sum_inr (I := 𝓡∂ 3)
          (M := Σ w : {w // w ≠ endpoint s false}, PuncturedFactor N endpoint chart w.val)
          (N := {y : Z.Carrier // y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1}) ⟨⟨v, hv⟩, x⟩)
      exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp (f := Sigma.mk v) (x := x)
        (heq.symm ▸ hcomp) (isLocalDiffeomorph_sigmaMk (I := 𝓡∂ 3) v x)
  exact DifferentialGeometry.isLocalDiffeomorph_restrict_open (seamCore N endpoint chart hdisj s) hf

end DifferentialGeometry.Topology.PairedBallGluing

namespace DifferentialGeometry.Topology.PairedBallGluing

universe u v w
variable {V : Type v} {E : Type w}
  (N : V → ConnectedClosedOrientedManifold.{u} 3)
  (endpoint : E → Bool → V)
  (chart : (e : E) → (b : Bool) →
    OrientedBallChart (N (endpoint e b)).toClosedOrientedManifold)
  (s : E) (hloop : endpoint s true = endpoint s false)
  (hdisj : Pairwise fun p q =>
    Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
      (flagMap N endpoint chart q '' closedBall (0 : E3) 2))

private theorem radialPoint_cast_val (e : E) (b : Bool) (v : V) (hv : endpoint e b = v)
    (z : sphere (0 : E3) 1) (r : ℝ) (hr : r ∈ Icc 1 2) :
    (hv ▸ radialPoint N endpoint chart hdisj e b z r hr).val =
      (incidenceChart N endpoint chart v ⟨(e, b), hv⟩).chart (r • z.val) := by
  subst v
  rfl

private theorem radialPoint_cast_sigma (e : E) (b : Bool) (v : V) (hv : endpoint e b = v)
    (z : sphere (0 : E3) 1) (r : ℝ) (hr : r ∈ Icc 1 2) :
    (⟨v, hv ▸ radialPoint N endpoint chart hdisj e b z r hr⟩ :
      Σ v, PuncturedFactor N endpoint chart v) =
      ⟨endpoint e b, radialPoint N endpoint chart hdisj e b z r hr⟩ := by
  subst v
  rfl

variable (a : BoundaryAttachment)
  (S : SmoothSelfAttachment (chart s false) (loopSecondChart N endpoint chart s hloop)
    (disjoint_loop_charts N endpoint chart s hloop hdisj) a)
  {Z : ClosedOrientedManifold.{u} 3}
  (F : ClosedOrientedManifold.OrientedDiffeomorph S.toConnectedClosedOrientedManifold.toClosedOrientedManifold Z)
  {ι : Type*} (b : ι → OrientedBallChart Z)
  {Y : Type*}
  (H : Quot (seamRel N endpoint chart hdisj s a) →
    {y : Z.Carrier // y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1} ⊕ Y)
  (hH : ∀ x : PuncturedFactor N endpoint chart (endpoint s false),
    ∃ y, H (Quot.mk _ ⟨endpoint s false, x⟩) = Sum.inl y ∧
      y.val = F.val (SelfAttachment.coreToBand (chart s false).toBallChart
        (loopSecondChart N endpoint chart s hloop).toBallChart
        (disjoint_loop_charts N endpoint chart s hloop hdisj) a.val.toHomeomorph
        (loopPuncturedFactorHomeomorph N endpoint chart s hloop x).val))

include hH in
theorem loop_seamChart_image (p : SelfAttachment.directSeamDomain) :
    ∃ y, H (seamChart N endpoint chart hdisj s a p) = Sum.inl y ∧
      y.val = F.val (SelfAttachment.bandInteriorInclusion (chart s false).toBallChart
        (loopSecondChart N endpoint chart s hloop).toBallChart
        (disjoint_loop_charts N endpoint chart s hloop hdisj) a.val.toHomeomorph
        ⟨(p.val.1, 1 / 2 - p.val.2), mem_univ _,
          by constructor <;> linarith [p.property.2.1, p.property.2.2]⟩) := by
  have hseam := SelfAttachment.directToBand_directSeam (chart s false).toBallChart
    (loopSecondChart N endpoint chart s hloop).toBallChart
    (disjoint_loop_charts N endpoint chart s hloop hdisj) a.val.toHomeomorph p
  by_cases ht : 0 ≤ p.val.2
  · let hr : 1 + p.val.2 ∈ Icc 1 2 := ⟨by linarith, by linarith [p.property.2.2]⟩
    obtain ⟨y, hy, hyval⟩ := hH (radialPoint N endpoint chart hdisj s false p.val.1 (1 + p.val.2) hr)
    refine ⟨y, ?_, hyval.trans ?_⟩
    · simpa only [seamChart, dite_eq_left ht] using hy
    · apply congrArg F.val
      rw [SelfAttachment.directSeam, dite_eq_left ht] at hseam
      exact hseam
  · let hr : 1 - p.val.2 ∈ Icc 1 2 := ⟨by linarith, by linarith [p.property.2.1]⟩
    let x : PuncturedFactor N endpoint chart (endpoint s false) :=
      hloop ▸ radialPoint N endpoint chart hdisj s true (a.val p.val.1) (1 - p.val.2) hr
    obtain ⟨y, hy, hyval⟩ := hH x
    have hx : (⟨endpoint s false, x⟩ : Σ v, PuncturedFactor N endpoint chart v) =
        ⟨endpoint s true, radialPoint N endpoint chart hdisj s true (a.val p.val.1) (1 - p.val.2) hr⟩ :=
      radialPoint_cast_sigma N endpoint chart hdisj s true (endpoint s false) hloop _ _ _
    refine ⟨y, ?_, hyval.trans ?_⟩
    · rw [seamChart, dite_eq_right ht]
      exact (congrArg (fun q => H (Quot.mk _ q)) hx).symm.trans hy
    · apply congrArg F.val
      rw [SelfAttachment.directSeam, dite_eq_right ht] at hseam
      have hxval : (loopPuncturedFactorHomeomorph N endpoint chart s hloop x).val =
          (chart s false).toBallChart.secondRadialMap
            (loopSecondChart N endpoint chart s hloop).toBallChart
            (disjoint_loop_charts N endpoint chart s hloop hdisj)
            (a.val p.val.1) (1 - p.val.2) hr := by
        apply Subtype.ext
        exact radialPoint_cast_val N endpoint chart hdisj s true (endpoint s false) hloop _ _ _
      rw [hxval]
      exact hseam

end DifferentialGeometry.Topology.PairedBallGluing

namespace DifferentialGeometry.Topology.PairedBallGluing

universe u v w
variable {V : Type v} {E : Type w}
  (N : V → ConnectedClosedOrientedManifold.{u} 3)
  (endpoint : E → Bool → V)
  (chart : (e : E) → (b : Bool) →
    OrientedBallChart (N (endpoint e b)).toClosedOrientedManifold)
  (s : E) (hloop : endpoint s true = endpoint s false)
  (hdisj : Pairwise fun p q =>
    Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
      (flagMap N endpoint chart q '' closedBall (0 : E3) 2))
  (a : BoundaryAttachment)
  (S : SmoothSelfAttachment (chart s false) (loopSecondChart N endpoint chart s hloop)
    (disjoint_loop_charts N endpoint chart s hloop hdisj) a)
  {Z : ClosedOrientedManifold.{u} 3}
  (F : ClosedOrientedManifold.OrientedDiffeomorph S.toConnectedClosedOrientedManifold.toClosedOrientedManifold Z)
  {ι : Type*} [Finite ι] (b : ι → OrientedBallChart Z)
  (hb : ∀ i, (b i).chart '' closedBall (0 : E3) 1 ⊆
    range (F.val ∘ SelfAttachment.coreInclusion (chart s false).toBallChart
      (loopSecondChart N endpoint chart s hloop).toBallChart
      (disjoint_loop_charts N endpoint chart s hloop hdisj) a.val.toHomeomorph))
  (C : SmoothBoundaryAtlas (𝓡 3) 3 {y : Z.Carrier | y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1})
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace (EuclideanHalfSpace 3) Y] [IsManifold (𝓡∂ 3) ∞ Y]
  (H : Quot (seamRel N endpoint chart hdisj s a) →
    {y : Z.Carrier // y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1} ⊕ Y)
  (hH : ∀ x : PuncturedFactor N endpoint chart (endpoint s false),
    ∃ y, H (Quot.mk _ ⟨endpoint s false, x⟩) = Sum.inl y ∧
      y.val = F.val (SelfAttachment.coreToBand (chart s false).toBallChart
        (loopSecondChart N endpoint chart s hloop).toBallChart
        (disjoint_loop_charts N endpoint chart s hloop hdisj) a.val.toHomeomorph
        (loopPuncturedFactorHomeomorph N endpoint chart s hloop x).val))

include hH hb in
theorem loop_seamChart_isLocalDiffeomorph :
    let _ : ChartedSpace (EuclideanHalfSpace 3) {y : Z.Carrier // y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1} := C.toChartedSpace
    IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 3) ∞ (H ∘ seamChart N endpoint chart hdisj s a) := by
  let _ : ChartedSpace (EuclideanHalfSpace 3) {y : Z.Carrier // y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1} := C.toChartedSpace
  let _ : IsManifold (𝓡∂ 3) ∞ {y : Z.Carrier // y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1} := C.isManifold
  dsimp only
  have heq : (H ∘ seamChart N endpoint chart hdisj s a) = Sum.inl ∘ S.directSeamComplement F b hb := by
    funext p
    obtain ⟨y, hy, hval⟩ := loop_seamChart_image N endpoint chart s hloop hdisj a S F b H hH p
    exact hy.trans (congrArg Sum.inl (Subtype.ext hval))
  exact heq.symm ▸ DifferentialGeometry.isLocalDiffeomorph_comp
    (isLocalDiffeomorph_sum_inl (I := 𝓡∂ 3) (N := Y))
    (S.directSeamComplement_isLocalDiffeomorph F b hb C)

end DifferentialGeometry.Topology.PairedBallGluing

namespace DifferentialGeometry.Topology.PairedBallGluing

universe u v w
variable {V : Type v} {E : Type w}
  (N : V → ConnectedClosedOrientedManifold.{u} 3)
  (endpoint : E → Bool → V)
  (chart : (e : E) → (b : Bool) →
    OrientedBallChart (N (endpoint e b)).toClosedOrientedManifold)
  (s : E) (hloop : endpoint s true = endpoint s false)
  (b : {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s false} →
    OrientedBallChart (loopFactor N endpoint s none).toClosedOrientedManifold)
  (C : ∀ v, SmoothBoundaryAtlas (𝓡 3) 3
    {x : (N v).Carrier | (⟨v, x⟩ : Σ v, (N v).Carrier) ∉ ⋃ p, flagMap N endpoint chart p '' ball (0 : E3) 1})
  (D : SmoothBoundaryAtlas (𝓡 3) 3
    {y : (loopFactor N endpoint s none).Carrier | y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1})
  (C' : ∀ v, SmoothBoundaryAtlas (𝓡 3) 3
    {x : (loopFactor N endpoint s v).Carrier |
      (⟨v, x⟩ : Σ v, (loopFactor N endpoint s v).Carrier) ∉
        ⋃ p, flagMap (loopFactor N endpoint s)
          (fun e t => (loopFlag N endpoint chart s b e t).fst)
          (fun e t => (loopFlag N endpoint chart s b e t).snd) p '' ball (0 : E3) 1})

theorem loopPuncturedFactorHomeomorphSplit_isLocalDiffeomorph :
    let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3) (PuncturedFactor N endpoint chart v) := fun v => (C v).toChartedSpace
    let _ : ChartedSpace (EuclideanHalfSpace 3) {y : (loopFactor N endpoint s none).Carrier // y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1} := D.toChartedSpace
    let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3)
      (PuncturedFactor (loopFactor N endpoint s)
        (fun e t => (loopFlag N endpoint chart s b e t).fst)
        (fun e t => (loopFlag N endpoint chart s b e t).snd) v) := fun v => (C' v).toChartedSpace
    IsLocalDiffeomorph (𝓡∂ 3) (𝓡∂ 3) ∞ (loopPuncturedFactorHomeomorphSplit N endpoint chart s b hloop) := by
  let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3) (PuncturedFactor N endpoint chart v) := fun v => (C v).toChartedSpace
  let _ : ∀ v, IsManifold (𝓡∂ 3) ∞ (PuncturedFactor N endpoint chart v) := fun v => (C v).isManifold
  let _ : ChartedSpace (EuclideanHalfSpace 3) {y : (loopFactor N endpoint s none).Carrier // y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1} := D.toChartedSpace
  let _ : IsManifold (𝓡∂ 3) ∞ {y : (loopFactor N endpoint s none).Carrier // y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1} := D.isManifold
  let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3)
    (PuncturedFactor (loopFactor N endpoint s)
      (fun e t => (loopFlag N endpoint chart s b e t).fst)
      (fun e t => (loopFlag N endpoint chart s b e t).snd) v) := fun v => (C' v).toChartedSpace
  let _ : ∀ v, IsManifold (𝓡∂ 3) ∞
    (PuncturedFactor (loopFactor N endpoint s)
      (fun e t => (loopFlag N endpoint chart s b e t).fst)
      (fun e t => (loopFlag N endpoint chart s b e t).snd) v) := fun v => (C' v).isManifold
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
      (fun x => not_congr (Set.ext_iff.mp (loopFlag_holes_none N endpoint chart s b (ball 0 1)) x))
    have heq : loopPuncturedFactorHomeomorphSplit N endpoint chart s b hloop ∘ Sigma.mk none =
        Sum.inl ∘ T := by funext x; rfl
    rw [heq]
    exact DifferentialGeometry.isLocalDiffeomorph_comp isLocalDiffeomorph_sum_inl T.isLocalDiffeomorph
  | some v =>
    let _ := (C' (some v)).toChartedSpace
    let _ := (C' (some v)).isManifold
    let _ := (C v.val).toChartedSpace
    let _ := (C v.val).isManifold
    let T := (C' (some v)).diffeomorphOfAmbient (C v.val) (Diffeomorph.refl (𝓡 3) _ ∞)
      (fun x => not_congr (Set.ext_iff.mp (loopFlag_holes_some N endpoint chart s b hloop v (ball 0 1)) x))
    have heq : loopPuncturedFactorHomeomorphSplit N endpoint chart s b hloop ∘ Sigma.mk (some v) =
        Sum.inr ∘ (Sigma.mk v ∘ T) := by funext x; rfl
    rw [heq]
    exact DifferentialGeometry.isLocalDiffeomorph_comp isLocalDiffeomorph_sum_inr
      (DifferentialGeometry.isLocalDiffeomorph_comp (isLocalDiffeomorph_sigmaMk v) T.isLocalDiffeomorph)

end DifferentialGeometry.Topology.PairedBallGluing

namespace DifferentialGeometry.Topology.PairedBallGluing

universe u v w
variable {V : Type v} {E : Type w}
  (N : V → ConnectedClosedOrientedManifold.{u} 3)
  (endpoint : E → Bool → V)
  (chart : (e : E) → (b : Bool) →
    OrientedBallChart (N (endpoint e b)).toClosedOrientedManifold)
  (s : E) (hloop : endpoint s true = endpoint s false)
  (hdisj : Pairwise fun p q =>
    Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
      (flagMap N endpoint chart q '' closedBall (0 : E3) 2))

variable (a : BoundaryAttachment)
  (S : SmoothSelfAttachment (chart s false) (loopSecondChart N endpoint chart s hloop)
    (disjoint_loop_charts N endpoint chart s hloop hdisj) a)
  {Z : ClosedOrientedManifold.{u} 3}
  (F : ClosedOrientedManifold.OrientedDiffeomorph S.toConnectedClosedOrientedManifold.toClosedOrientedManifold Z)
  (b : {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s false} → OrientedBallChart Z)
  (hb : ∀ i x, x ∈ closedBall (0 : E3) 2 →
    ∃ hx : (remainingIncidenceChart N endpoint chart s (endpoint s false) i).chart x ∈
      ((chart s false).chart '' ball 0 1 ∪ (loopSecondChart N endpoint chart s hloop).chart '' ball 0 1)ᶜ,
      (b i).chart x = F.val (SelfAttachment.coreInclusion (chart s false).toBallChart
        (loopSecondChart N endpoint chart s hloop).toBallChart
        (disjoint_loop_charts N endpoint chart s hloop hdisj) a.val.toHomeomorph
        ⟨(remainingIncidenceChart N endpoint chart s (endpoint s false) i).chart x, hx⟩))
  (C : ∀ v, SmoothBoundaryAtlas (𝓡 3) 3
    {x : (N v).Carrier | (⟨v, x⟩ : Σ v, (N v).Carrier) ∉ ⋃ p, flagMap N endpoint chart p '' ball (0 : E3) 1})
  (D : SmoothBoundaryAtlas (𝓡 3) 3 {y : Z.Carrier | y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1})
  (H : Quot (seamRel N endpoint chart hdisj s a) →
    {y : Z.Carrier // y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1} ⊕
      (Σ v : {v // v ≠ endpoint s false}, PuncturedFactor N endpoint chart v.val))
  (hH : ∀ x : PuncturedFactor N endpoint chart (endpoint s false),
    ∃ y, H (Quot.mk _ ⟨endpoint s false, x⟩) = Sum.inl y ∧
      y.val = F.val (SelfAttachment.coreToBand (chart s false).toBallChart
        (loopSecondChart N endpoint chart s hloop).toBallChart
        (disjoint_loop_charts N endpoint chart s hloop hdisj) a.val.toHomeomorph
        (loopPuncturedFactorHomeomorph N endpoint chart s hloop x).val))
  (hR : ∀ (v : {v // v ≠ endpoint s false}) (x : PuncturedFactor N endpoint chart v.val),
    H (Quot.mk _ ⟨v.val, x⟩) = Sum.inr ⟨v, x⟩)


variable [Finite E]

include hb hH hR in
theorem exists_loop_split_smooth_atlas :
    let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3) (PuncturedFactor N endpoint chart v) := fun v => (C v).toChartedSpace
    let _ : ChartedSpace (EuclideanHalfSpace 3) {y : Z.Carrier // y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1} := D.toChartedSpace
    ∀ h : Quot (seamRel N endpoint chart hdisj s a) ≃ₜ
      {y : Z.Carrier // y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1} ⊕
        (Σ v : {v // v ≠ endpoint s false}, PuncturedFactor N endpoint chart v.val),
    (∀ x, h x = H x) →
    ∃ A : ChartedSpace (EuclideanHalfSpace 3) (Quot (seamRel N endpoint chart hdisj s a)),
      let _ := A
      IsManifold (𝓡∂ 3) ∞ (Quot (seamRel N endpoint chart hdisj s a)) ∧
        IsLocalDiffeomorph (𝓡∂ 3) (𝓡∂ 3) ∞ (seamCoreInclusion N endpoint chart hdisj s a) ∧
        IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 3) ∞ (seamChart N endpoint chart hdisj s a) ∧
        ∃ G : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) (Quot (seamRel N endpoint chart hdisj s a))
          ({y : Z.Carrier // y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1} ⊕
            (Σ v : {v // v ≠ endpoint s false}, PuncturedFactor N endpoint chart v.val)) ∞,
          ∀ x, G x = H x := by
  let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3) (PuncturedFactor N endpoint chart v) := fun v => (C v).toChartedSpace
  let _ : ∀ v, IsManifold (𝓡∂ 3) ∞ (PuncturedFactor N endpoint chart v) := fun v => (C v).isManifold
  let _ : ChartedSpace (EuclideanHalfSpace 3) {y : Z.Carrier // y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1} := D.toChartedSpace
  let _ : IsManifold (𝓡∂ 3) ∞ {y : Z.Carrier // y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1} := D.isManifold
  dsimp only
  intro h heq
  have hbcore : ∀ i, (b i).chart '' closedBall (0 : E3) 1 ⊆
      range (F.val ∘ SelfAttachment.coreInclusion (chart s false).toBallChart
        (loopSecondChart N endpoint chart s hloop).toBallChart
        (disjoint_loop_charts N endpoint chart s hloop hdisj) a.val.toHomeomorph) := by
    rintro i _ ⟨x, hx, rfl⟩
    obtain ⟨hx', hb'⟩ := hb i x (closedBall_subset_closedBall (by norm_num) hx)
    exact ⟨⟨_, hx'⟩, hb'.symm⟩
  have hcore := loop_seamCore_isLocalDiffeomorph N endpoint chart s hloop hdisj a S F b hb C D H hH hR
  have hseam := loop_seamChart_isLocalDiffeomorph N endpoint chart s hloop hdisj a S F b hbcore D H hH
  have heq' : (h : _ → _) = H := funext heq
  obtain ⟨A, hA, hc, hs, G, hG⟩ := exists_smooth_seam_atlas_of_comp_local_maps
    N endpoint chart hdisj s a h (heq'.symm ▸ hcore) (heq'.symm ▸ hseam)
  exact ⟨A, hA, hc, hs, G, fun x => (hG x).trans (heq x)⟩

end DifferentialGeometry.Topology.PairedBallGluing

namespace DifferentialGeometry.Topology.PairedBallGluing

universe u v w
variable {V : Type v} {E : Type w} [Finite E]
  (N : V → ConnectedClosedOrientedManifold.{u} 3)
  (endpoint : E → Bool → V)
  (chart : (e : E) → (b : Bool) →
    OrientedBallChart (N (endpoint e b)).toClosedOrientedManifold)
  (s : E) (hloop : endpoint s true = endpoint s false)
  (hdisj : Pairwise fun p q =>
    Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
      (flagMap N endpoint chart q '' closedBall (0 : E3) 2))
  (S : SmoothSelfAttachment (chart s false) (loopSecondChart N endpoint chart s hloop)
    (disjoint_loop_charts N endpoint chart s hloop hdisj) boundaryAttachment)
  (F : ClosedOrientedManifold.OrientedDiffeomorph S.toConnectedClosedOrientedManifold.toClosedOrientedManifold
    (loopFactor N endpoint s none).toClosedOrientedManifold)
  (b : {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s false} →
    OrientedBallChart (loopFactor N endpoint s none).toClosedOrientedManifold)
  (hb : ∀ i x, x ∈ closedBall (0 : E3) 2 →
    ∃ hx : (remainingIncidenceChart N endpoint chart s (endpoint s false) i).chart x ∈
      ((chart s false).chart '' ball 0 1 ∪ (loopSecondChart N endpoint chart s hloop).chart '' ball 0 1)ᶜ,
      (b i).chart x = F.val (SelfAttachment.coreInclusion (chart s false).toBallChart
        (loopSecondChart N endpoint chart s hloop).toBallChart
        (disjoint_loop_charts N endpoint chart s hloop hdisj) boundaryAttachment.val.toHomeomorph
        ⟨(remainingIncidenceChart N endpoint chart s (endpoint s false) i).chart x, hx⟩))
  (C : ∀ v, SmoothBoundaryAtlas (𝓡 3) 3
    {x : (N v).Carrier | (⟨v, x⟩ : Σ v, (N v).Carrier) ∉ ⋃ p, flagMap N endpoint chart p '' ball (0 : E3) 1})
  (D : SmoothBoundaryAtlas (𝓡 3) 3
    {y : (loopFactor N endpoint s none).Carrier | y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1})
  (C' : ∀ v, SmoothBoundaryAtlas (𝓡 3) 3
    {x : (loopFactor N endpoint s v).Carrier |
      (⟨v, x⟩ : Σ v, (loopFactor N endpoint s v).Carrier) ∉
        ⋃ p, flagMap (loopFactor N endpoint s)
          (fun e t => (loopFlag N endpoint chart s b e t).fst)
          (fun e t => (loopFlag N endpoint chart s b e t).snd) p '' ball (0 : E3) 1})
  (H : Quot (seamRel N endpoint chart hdisj s boundaryAttachment) ≃ₜ
    (Σ v, PuncturedFactor (loopFactor N endpoint s)
      (fun e t => (loopFlag N endpoint chart s b e t).fst)
      (fun e t => (loopFlag N endpoint chart s b e t).snd) v))
  (hH : ∀ x : PuncturedFactor N endpoint chart (endpoint s false),
    ∃ y, loopPuncturedFactorHomeomorphSplit N endpoint chart s b hloop (H (Quot.mk _ ⟨endpoint s false, x⟩)) = Sum.inl y ∧
      y.val = F.val (SelfAttachment.coreToBand (chart s false).toBallChart
        (loopSecondChart N endpoint chart s hloop).toBallChart
        (disjoint_loop_charts N endpoint chart s hloop hdisj) boundaryAttachment.val.toHomeomorph
        (loopPuncturedFactorHomeomorph N endpoint chart s hloop x).val))
  (hR : ∀ (v : {v // v ≠ endpoint s false}) (x : PuncturedFactor N endpoint chart v.val),
    loopPuncturedFactorHomeomorphSplit N endpoint chart s b hloop (H (Quot.mk _ ⟨v.val, x⟩)) = Sum.inr ⟨v, x⟩)

include hb hH hR D in
theorem exists_loop_smooth_atlas_of_representatives :
    let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3) (PuncturedFactor N endpoint chart v) := fun v => (C v).toChartedSpace
    let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3)
      (PuncturedFactor (loopFactor N endpoint s)
        (fun e t => (loopFlag N endpoint chart s b e t).fst)
        (fun e t => (loopFlag N endpoint chart s b e t).snd) v) := fun v => (C' v).toChartedSpace
    ∃ A : ChartedSpace (EuclideanHalfSpace 3) (Quot (seamRel N endpoint chart hdisj s boundaryAttachment)),
      let _ := A
      IsManifold (𝓡∂ 3) ∞ (Quot (seamRel N endpoint chart hdisj s boundaryAttachment)) ∧
        IsLocalDiffeomorph (𝓡∂ 3) (𝓡∂ 3) ∞ (seamCoreInclusion N endpoint chart hdisj s boundaryAttachment) ∧
        IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 3) ∞ (seamChart N endpoint chart hdisj s boundaryAttachment) ∧
        ∃ G : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) (Quot (seamRel N endpoint chart hdisj s boundaryAttachment))
          (Σ v, PuncturedFactor (loopFactor N endpoint s)
            (fun e t => (loopFlag N endpoint chart s b e t).fst)
            (fun e t => (loopFlag N endpoint chart s b e t).snd) v) ∞,
          ∀ x, G x = H x := by
  let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3) (PuncturedFactor N endpoint chart v) := fun v => (C v).toChartedSpace
  let _ : ∀ v, IsManifold (𝓡∂ 3) ∞ (PuncturedFactor N endpoint chart v) := fun v => (C v).isManifold
  let _ : ChartedSpace (EuclideanHalfSpace 3) {y : (loopFactor N endpoint s none).Carrier // y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1} := D.toChartedSpace
  let _ : IsManifold (𝓡∂ 3) ∞ {y : (loopFactor N endpoint s none).Carrier // y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1} := D.isManifold
  let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3)
    (PuncturedFactor (loopFactor N endpoint s)
      (fun e t => (loopFlag N endpoint chart s b e t).fst)
      (fun e t => (loopFlag N endpoint chart s b e t).snd) v) := fun v => (C' v).toChartedSpace
  let _ : ∀ v, IsManifold (𝓡∂ 3) ∞
    (PuncturedFactor (loopFactor N endpoint s)
      (fun e t => (loopFlag N endpoint chart s b e t).fst)
      (fun e t => (loopFlag N endpoint chart s b e t).snd) v) := fun v => (C' v).isManifold
  dsimp only
  let J := loopPuncturedFactorHomeomorphSplit N endpoint chart s b hloop
  have hJ := loopPuncturedFactorHomeomorphSplit_isLocalDiffeomorph N endpoint chart s hloop b C D C'
  let E := hJ.diffeomorphOfBijective J.bijective
  let L := H.trans J
  obtain ⟨A, hA, hc, hs, G, hG⟩ := exists_loop_split_smooth_atlas
    N endpoint chart s hloop hdisj boundaryAttachment S F b hb C D L hH hR L (fun _ => rfl)
  let _ := A
  refine ⟨A, hA, hc, hs, G.trans E.symm, ?_⟩
  intro x
  change E.symm (G x) = H x
  apply E.injective
  exact (E.apply_symm_apply (G x)).trans (hG x)

end DifferentialGeometry.Topology.PairedBallGluing

namespace DifferentialGeometry.Topology.PairedBallGluing

universe u v w
variable {V : Type v} {E : Type w} [Finite E]
  (N : V → ConnectedClosedOrientedManifold.{u} 3)
  (endpoint : E → Bool → V)
  (chart : (e : E) → (b : Bool) →
    OrientedBallChart (N (endpoint e b)).toClosedOrientedManifold)
  (s : E) (hloop : endpoint s true = endpoint s false)
  (hdisj : Pairwise fun p q =>
    Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
      (flagMap N endpoint chart q '' closedBall (0 : E3) 2))
  (S : SmoothSelfAttachment (chart s false) (loopSecondChart N endpoint chart s hloop)
    (disjoint_loop_charts N endpoint chart s hloop hdisj) boundaryAttachment)
  (F : ClosedOrientedManifold.OrientedDiffeomorph S.toConnectedClosedOrientedManifold.toClosedOrientedManifold
    (loopFactor N endpoint s none).toClosedOrientedManifold)
  (b : {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s false} →
    OrientedBallChart (loopFactor N endpoint s none).toClosedOrientedManifold)
  (hb : ∀ i x, x ∈ closedBall (0 : E3) 2 →
    ∃ hx : (remainingIncidenceChart N endpoint chart s (endpoint s false) i).chart x ∈
      ((chart s false).chart '' ball 0 1 ∪ (loopSecondChart N endpoint chart s hloop).chart '' ball 0 1)ᶜ,
      (b i).chart x = F.val (SelfAttachment.coreInclusion (chart s false).toBallChart
        (loopSecondChart N endpoint chart s hloop).toBallChart
        (disjoint_loop_charts N endpoint chart s hloop hdisj) boundaryAttachment.val.toHomeomorph
        ⟨(remainingIncidenceChart N endpoint chart s (endpoint s false) i).chart x, hx⟩))
  (C : ∀ v, SmoothBoundaryAtlas (𝓡 3) 3
    {x : (N v).Carrier | (⟨v, x⟩ : Σ v, (N v).Carrier) ∉ ⋃ p, flagMap N endpoint chart p '' ball (0 : E3) 1})
  (C' : ∀ v, SmoothBoundaryAtlas (𝓡 3) 3
    {x : (loopFactor N endpoint s v).Carrier |
      (⟨v, x⟩ : Σ v, (loopFactor N endpoint s v).Carrier) ∉
        ⋃ p, flagMap (loopFactor N endpoint s)
          (fun e t => (loopFlag N endpoint chart s b e t).fst)
          (fun e t => (loopFlag N endpoint chart s b e t).snd) p '' ball (0 : E3) 1})
  (H : Quot (seamRel N endpoint chart hdisj s boundaryAttachment) ≃ₜ
    (Σ v, PuncturedFactor (loopFactor N endpoint s)
      (fun e t => (loopFlag N endpoint chart s b e t).fst)
      (fun e t => (loopFlag N endpoint chart s b e t).snd) v))
  (hH : ∀ x : PuncturedFactor N endpoint chart (endpoint s false),
    ∃ y, loopPuncturedFactorHomeomorphSplit N endpoint chart s b hloop (H (Quot.mk _ ⟨endpoint s false, x⟩)) = Sum.inl y ∧
      y.val = F.val (SelfAttachment.coreToBand (chart s false).toBallChart
        (loopSecondChart N endpoint chart s hloop).toBallChart
        (disjoint_loop_charts N endpoint chart s hloop hdisj) boundaryAttachment.val.toHomeomorph
        (loopPuncturedFactorHomeomorph N endpoint chart s hloop x).val))
  (hR : ∀ (v : {v // v ≠ endpoint s false}) (x : PuncturedFactor N endpoint chart v.val),
    loopPuncturedFactorHomeomorphSplit N endpoint chart s b hloop (H (Quot.mk _ ⟨v.val, x⟩)) = Sum.inr ⟨v, x⟩)

include hb hH hR in
theorem exists_loop_smooth_atlas_of_factor_representatives :
    let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3) (PuncturedFactor N endpoint chart v) := fun v => (C v).toChartedSpace
    let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3)
      (PuncturedFactor (loopFactor N endpoint s)
        (fun e t => (loopFlag N endpoint chart s b e t).fst)
        (fun e t => (loopFlag N endpoint chart s b e t).snd) v) := fun v => (C' v).toChartedSpace
    ∃ A : ChartedSpace (EuclideanHalfSpace 3) (Quot (seamRel N endpoint chart hdisj s boundaryAttachment)),
      let _ := A
      IsManifold (𝓡∂ 3) ∞ (Quot (seamRel N endpoint chart hdisj s boundaryAttachment)) ∧
        IsLocalDiffeomorph (𝓡∂ 3) (𝓡∂ 3) ∞ (seamCoreInclusion N endpoint chart hdisj s boundaryAttachment) ∧
        IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 3) ∞ (seamChart N endpoint chart hdisj s boundaryAttachment) ∧
        ∃ G : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) (Quot (seamRel N endpoint chart hdisj s boundaryAttachment))
          (Σ v, PuncturedFactor (loopFactor N endpoint s)
            (fun e t => (loopFlag N endpoint chart s b e t).fst)
            (fun e t => (loopFlag N endpoint chart s b e t).snd) v) ∞,
          ∀ x, G x = H x := by
  have hK : {x : (loopFactor N endpoint s none).Carrier |
      (⟨none, x⟩ : Σ v, (loopFactor N endpoint s v).Carrier) ∉
        ⋃ p, flagMap (loopFactor N endpoint s)
          (fun e t => (loopFlag N endpoint chart s b e t).fst)
          (fun e t => (loopFlag N endpoint chart s b e t).snd) p '' ball (0 : E3) 1} =
      {y : (loopFactor N endpoint s none).Carrier | y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1} := by
    ext x
    exact not_congr (Set.ext_iff.mp (loopFlag_holes_none N endpoint chart s b (ball 0 1)) x)
  let D : SmoothBoundaryAtlas (𝓡 3) 3 {y : (loopFactor N endpoint s none).Carrier |
      y ∉ ⋃ i, (b i).chart '' ball (0 : E3) 1} := hK ▸ C' none
  exact exists_loop_smooth_atlas_of_representatives N endpoint chart s hloop hdisj S F b hb C D C' H hH hR

end DifferentialGeometry.Topology.PairedBallGluing

namespace DifferentialGeometry.Topology.PairedBallGluing

universe u v w
variable {V : Type v} {E : Type w} [Finite E]
  (N : V → ConnectedClosedOrientedManifold.{u} 3)
  (endpoint : E → Bool → V)
  (chart : (e : E) → (b : Bool) →
    OrientedBallChart (N (endpoint e b)).toClosedOrientedManifold)
  (s : E) (hloop : endpoint s true = endpoint s false)
  (hdisj : Pairwise fun p q =>
    Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
      (flagMap N endpoint chart q '' closedBall (0 : E3) 2))
  (C : ∀ v, SmoothBoundaryAtlas (𝓡 3) 3
    {x : (N v).Carrier | (⟨v, x⟩ : Σ v, (N v).Carrier) ∉ ⋃ p, flagMap N endpoint chart p '' ball (0 : E3) 1})

theorem exists_smooth_loop_homeomorph :
    let p := chart s false
    let q := loopSecondChart N endpoint chart s hloop
    let hd := disjoint_loop_charts N endpoint chart s hloop hdisj
    let e := remainingIncidenceChart N endpoint chart s (endpoint s false)
    ∃ S : SmoothSelfAttachment p q hd boundaryAttachment,
    ∃ F : ClosedOrientedManifold.OrientedDiffeomorph
      S.toConnectedClosedOrientedManifold.toClosedOrientedManifold
      (connectedSum (N (endpoint s false)) sphereTwoTimesCircleLift).toClosedOrientedManifold,
    ∃ b : {p : E × Bool // p.1 ≠ s ∧ endpoint p.1 p.2 = endpoint s false} →
      OrientedBallChart
        (connectedSum (N (endpoint s false)) sphereTwoTimesCircleLift).toClosedOrientedManifold,
      (∀ i x, x ∈ closedBall (0 : E3) 2 →
        ∃ hx : (e i).chart x ∈ (p.chart '' ball 0 1 ∪ q.chart '' ball 0 1)ᶜ,
          (b i).chart x = F.val (SelfAttachment.coreInclusion p.toBallChart q.toBallChart hd
            boundaryAttachment.val.toHomeomorph ⟨(e i).chart x, hx⟩)) ∧
      ∃ hb : Pairwise fun p q =>
        Disjoint (flagMap (loopFactor N endpoint s)
          (fun e t => (loopFlag N endpoint chart s b e t).fst)
          (fun e t => (loopFlag N endpoint chart s b e t).snd) p '' closedBall (0 : E3) 2)
        (flagMap (loopFactor N endpoint s)
          (fun e t => (loopFlag N endpoint chart s b e t).fst)
          (fun e t => (loopFlag N endpoint chart s b e t).snd) q '' closedBall (0 : E3) 2),
        ∃ H : Quot (seamRel N endpoint chart hdisj s boundaryAttachment) ≃ₜ
          (Σ v, PuncturedFactor (loopFactor N endpoint s)
            (fun e t => (loopFlag N endpoint chart s b e t).fst)
            (fun e t => (loopFlag N endpoint chart s b e t).snd) v),
          (∀ C' : ∀ v, SmoothBoundaryAtlas (𝓡 3) 3
            {x : (loopFactor N endpoint s v).Carrier |
              (⟨v, x⟩ : Σ v, (loopFactor N endpoint s v).Carrier) ∉
                ⋃ p, flagMap (loopFactor N endpoint s)
                  (fun e t => (loopFlag N endpoint chart s b e t).fst)
                  (fun e t => (loopFlag N endpoint chart s b e t).snd) p '' ball (0 : E3) 1},
            let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3) (PuncturedFactor N endpoint chart v) := fun v => (C v).toChartedSpace
            let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3)
              (PuncturedFactor (loopFactor N endpoint s)
                (fun e t => (loopFlag N endpoint chart s b e t).fst)
                (fun e t => (loopFlag N endpoint chart s b e t).snd) v) := fun v => (C' v).toChartedSpace
            ∃ A : ChartedSpace (EuclideanHalfSpace 3) (Quot (seamRel N endpoint chart hdisj s boundaryAttachment)),
              let _ := A
              IsManifold (𝓡∂ 3) ∞ (Quot (seamRel N endpoint chart hdisj s boundaryAttachment)) ∧
                IsLocalDiffeomorph (𝓡∂ 3) (𝓡∂ 3) ∞ (seamCoreInclusion N endpoint chart hdisj s boundaryAttachment) ∧
                IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 3) ∞ (seamChart N endpoint chart hdisj s boundaryAttachment) ∧
                ∃ G : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) (Quot (seamRel N endpoint chart hdisj s boundaryAttachment))
                  (Σ v, PuncturedFactor (loopFactor N endpoint s)
                    (fun e t => (loopFlag N endpoint chart s b e t).fst)
                    (fun e t => (loopFlag N endpoint chart s b e t).snd) v) ∞,
                  ∀ x, G x = H x) ∧
          (∀ x : PuncturedFactor N endpoint chart (endpoint s false),
            ∃ y, loopPuncturedFactorHomeomorphSplit N endpoint chart s b hloop
                (H (Quot.mk _ ⟨endpoint s false, x⟩)) = Sum.inl y ∧
              y.val = F.val (SelfAttachment.coreToBand p.toBallChart q.toBallChart hd
                boundaryAttachment.val.toHomeomorph
                (loopPuncturedFactorHomeomorph N endpoint chart s hloop x).val)) ∧
          (∀ (v : {v // v ≠ endpoint s false}) (x : PuncturedFactor N endpoint chart v.val),
            loopPuncturedFactorHomeomorphSplit N endpoint chart s b hloop
              (H (Quot.mk _ ⟨v.val, x⟩)) = Sum.inr ⟨v, x⟩) ∧
          ∀ (e : {e // e ≠ s}) (t : Bool) (z : sphere (0 : E3) 1),
            H (Quot.mk _ ⟨endpoint e.val t, boundaryPoint N endpoint chart hdisj e.val t z⟩) =
              ⟨(loopFlag N endpoint chart s b e t).fst,
                boundaryPoint (loopFactor N endpoint s)
                  (fun e t => (loopFlag N endpoint chart s b e t).fst)
                  (fun e t => (loopFlag N endpoint chart s b e t).snd) hb e t z⟩ := by
  dsimp only
  obtain ⟨S, F, b, hb, hb', H, hH, hR, hboundary⟩ :=
    exists_loop_homeomorph N endpoint chart s hloop hdisj
  refine ⟨S, F, b, hb, hb', H, ?_, hH, hR, hboundary⟩
  intro C'
  exact exists_loop_smooth_atlas_of_factor_representatives
    N endpoint chart s hloop hdisj S F b hb C C' H hH hR

end DifferentialGeometry.Topology.PairedBallGluing
