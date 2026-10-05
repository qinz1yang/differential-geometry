import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutOrientCharts
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.ConnectedSumFixedFold

/-!
# Chapter-14 assembly, L2 COMPARE A6-b, part 3: orientation signs

Lane ASM-L2d.

* `exists_orientation_map_comp`: pointwise orientation-preserving differentials compose;
* `SphereCutCapped.orientation_map_of_eventuallyEq_coreFold`: a local diffeomorphism from the
  interior of a ball chart of a closed component model to the closed model of `W` which near a
  point equals `coreFold` (the fold read through the core) and whose point is the core image of an
  interior point, is orientation preserving there (closed-model orientations: B0 pull-backs);
* `connectedSumFoldDiffeomorph_right_orientation`: if the fold diffeomorphism of a connected sum
  is orientation preserving, so is the right factor map at every interior point;
* `false_of_connectedSumFold_mixed`: a fold whose left factor map is positive at one point and whose
  right factor map is negative at one point does not exist (the connected sum is connected).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

section Comp

variable {E H E' H' E'' H'' M N P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'} {K : ModelWithCorners ℝ E'' H''}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
  [TopologicalSpace P] [ChartedSpace H'' P]

/-- Pointwise orientation-preserving differentials compose. -/
theorem exists_orientation_map_comp {f : M → N} {g : N → P} {x : M}
    (hf : MDifferentiableAt I J f x) (hg : MDifferentiableAt J K g (f x))
    {o₁ : Orientation ℝ (TangentSpace I x) (Fin 3)} {o₂ : Orientation ℝ (TangentSpace J (f x)) (Fin 3)}
    {o₃ : Orientation ℝ (TangentSpace K (g (f x))) (Fin 3)}
    (h₁ : ∃ L : TangentSpace I x ≃ₗ[ℝ] TangentSpace J (f x),
      (∀ v, L v = mfderiv I J f x v) ∧ Orientation.map (Fin 3) L o₁ = o₂)
    (h₂ : ∃ L : TangentSpace J (f x) ≃ₗ[ℝ] TangentSpace K (g (f x)),
      (∀ v, L v = mfderiv J K g (f x) v) ∧ Orientation.map (Fin 3) L o₂ = o₃) :
    ∃ L : TangentSpace I x ≃ₗ[ℝ] TangentSpace K ((g ∘ f) x),
      (∀ v, L v = mfderiv I K (g ∘ f) x v) ∧ Orientation.map (Fin 3) L o₁ = o₃ := by
  obtain ⟨L₁, hL₁, ho₁⟩ := h₁
  obtain ⟨L₂, hL₂, ho₂⟩ := h₂
  refine ⟨L₁.trans L₂, fun v => ?_, ?_⟩
  · rw [mfderiv_comp_apply x hg hf, LinearEquiv.trans_apply, hL₂, hL₁]
  · rw [orientation_map_trans_fin_three, ho₁, ho₂]

/-- An orientation-preserving diffeomorphism, pointwise. -/
theorem exists_orientation_map_of_preservesOrientation
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I ∞ M] [IsManifold J ∞ N]
    (e : M ≃ₘ⟮I, J⟯ N) {oM : ManifoldOrientation I M 3} {oN : ManifoldOrientation J N 3}
    (he : e.preservesOrientation oM oN) (x : M) :
    ∃ L : TangentSpace I x ≃ₗ[ℝ] TangentSpace J (e x),
      (∀ v, L v = mfderiv I J e x v) ∧ Orientation.map (Fin 3) L (oM.orientation x) =
        oN.orientation (e x) :=
  ⟨(e.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv, fun _ => rfl, he x⟩

/-- The inclusion of an open subset is orientation preserving for the restricted orientation. -/
theorem exists_orientation_map_subtype_val (U : TopologicalSpace.Opens M) (x : U)
    (o : Orientation ℝ (TangentSpace I (x : M)) (Fin 3)) :
    ∃ L : TangentSpace I x ≃ₗ[ℝ] TangentSpace I (Subtype.val x : M),
      (∀ v, L v = mfderiv I I (Subtype.val : U → M) x v) ∧ Orientation.map (Fin 3) L o = o :=
  ⟨LinearEquiv.refl ℝ E, fun v => (DifferentialGeometry.mfderiv_subtype_val_apply U x v).symm,
    by induction o using Module.Ray.ind with | h v hv => rfl⟩

/-- Transfer of a pointwise orientation statement along an equality of target points. -/
theorem orientation_map_eq_of_point_eq {x : M} {w w' : N} (hw : w = w')
    (A : TangentSpace I x ≃ₗ[ℝ] TangentSpace J w) (L : TangentSpace I x ≃ₗ[ℝ] TangentSpace J w')
    (h : ∀ v, A v = L v) (o : Orientation ℝ (TangentSpace I x) (Fin 3))
    (oN : (w : N) → Orientation ℝ (TangentSpace J w) (Fin 3))
    (hL : Orientation.map (Fin 3) L o = oN w') : Orientation.map (Fin 3) A o = oN w := by
  subst hw
  obtain rfl : A = L := LinearEquiv.ext h
  exact hL

end Comp

section Sign

variable (M N Q : ConnectedClosedOrientedManifold.{u} 3)
  (c : OrientedBallChart M.toClosedOrientedManifold)
  (d : OrientedBallChart N.toClosedOrientedManifold)
  (fL : c.toBallChart.Punctured → Q.Carrier) (fR : d.toBallChart.Punctured → Q.Carrier)
  (hcross : ∀ x y, fL x = fR y ↔ ∃ z,
    c.toBallChart.boundaryMap z = x ∧
      d.toBallChart.boundaryMap (boundaryAttachment.1 z) = y)
  (hiL : Injective fL) (hiR : Injective fR)
  (hcover : ∀ y : Q.Carrier, (∃ x, fL x = y) ∨ ∃ x, fR x = y)
  (hsL : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fL ∘ c.toBallChart.interiorToPunctured))
  (hsR : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fR ∘ d.toBallChart.interiorToPunctured))
  (hsC : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
    (connectedSumFoldCollar M N Q c d boundaryAttachment fL fR))

/-- If the fold diffeomorphism of a connected sum preserves orientation, the right factor map is
orientation preserving at every interior point. -/
theorem connectedSumFoldDiffeomorph_right_orientation
    (hF : (connectedSumFoldDiffeomorph M N Q c d boundaryAttachment fL fR hcross
      hiL hiR hcover hsL hsR hsC).preservesOrientation
        (smoothConnectedSum M N c d boundaryAttachment).orientation Q.orientation)
    (y : d.toBallChart.interior) :
    Orientation.map (Fin 3)
      ((hsR y).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
        (N.orientation.orientation y.val) =
          Q.orientation.orientation (fR (d.toBallChart.interiorToPunctured y)) := by
  let S := smoothConnectedSum M N c d boundaryAttachment
  let S' := S.toConnectedClosedOrientedManifold
  let F := connectedSumFoldDiffeomorph M N Q c d boundaryAttachment fL fR hcross
    hiL hiR hcover hsL hsR hsC
  let IR : d.toBallChart.interior → S'.Carrier :=
    ConnectedSumQuotient.interiorRight c.toBallChart d.toBallChart boundaryAttachment.1
  have hIR : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ IR := S.interiorRight_localDiffeomorph
  have hIRo : Orientation.map (Fin 3) ((hIR.mfderivToContinuousLinearEquiv (by simp) y).toLinearEquiv)
      (N.orientation.orientation y.val) = S'.orientation.orientation (IR y) :=
    S.interiorRight_preserves_orientation y
  let A := (hIR.mfderivToContinuousLinearEquiv (by simp) y).toLinearEquiv
  let B := (F.mfderivToContinuousLinearEquiv (by simp) (IR y)).toLinearEquiv
  let C := ((hsR y).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
  have hcomp : (F ∘ IR) = fR ∘ d.toBallChart.interiorToPunctured := by
    funext y
    rfl
  have hlin : A.trans B = C := by
    apply LinearEquiv.ext
    intro v
    change mfderiv (𝓡 3) (𝓡 3) F (IR y)
      (mfderiv (𝓡 3) (𝓡 3) IR y v) =
        mfderiv (𝓡 3) (𝓡 3) (fR ∘ d.toBallChart.interiorToPunctured) y v
    rw [← mfderiv_comp_apply y
      (F.contMDiff.mdifferentiableAt (by simp))
      (hIR.mdifferentiable (by simp) y)]
    exact congrArg (fun h => mfderiv (𝓡 3) (𝓡 3) h y v) hcomp
  change Orientation.map (Fin 3) C (N.orientation.orientation y.val) = _
  rw [← hlin]
  exact (orientation_map_trans_fin_three A B _).trans
    ((congrArg (Orientation.map (Fin 3) B) hIRo).trans (hF (IR y)))

include hcross hiL hiR hcover hsC in
/-- **Mixed signs are impossible.** A fold whose left factor map is orientation preserving at one
interior point cannot have a right factor map that is orientation reversing at an interior point. -/
theorem false_of_connectedSumFold_mixed
    (x : c.toBallChart.interior)
    (hp : Orientation.map (Fin 3)
      ((hsL x).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
        (M.orientation.orientation x.val) =
          Q.orientation.orientation (fL (c.toBallChart.interiorToPunctured x)))
    (y : d.toBallChart.interior)
    (hn : Orientation.map (Fin 3)
      ((hsR y).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
        (N.orientation.orientation y.val) =
          -Q.orientation.orientation (fR (d.toBallChart.interiorToPunctured y))) : False := by
  have hF := connectedSumFoldDiffeomorph_positive M N Q c d fL fR hcross hiL hiR hcover hsL hsR hsC
    x hp
  have h := connectedSumFoldDiffeomorph_right_orientation M N Q c d fL fR hcross hiL hiR hcover
    hsL hsR hsC hF y
  rw [h] at hn
  exact Module.Ray.ne_neg_self _ hn

end Sign

namespace SphereCutCapped

variable {W : CompactCarrier.{u}} {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}
  (X : SphereCutCapped W S E)

/-- `coreFold` is orientation preserving at the core image of an interior point (form with the
point as a variable). -/
theorem coreFold_oriented' {q : X.Q.Carrier}
    (hq : ∃ y, X.capping.core y = q ∧ X.C.model.IsInteriorPoint y) :
    ∃ L : TangentSpace X.Q.model q ≃ₗ[ℝ] TangentSpace W.model (X.coreFold q),
      (∀ v, L v = mfderiv X.Q.model W.model X.coreFold q v) ∧
      Orientation.map (Fin 3) L (X.Q.orientation.orientation q) =
        W.orientation.orientation (X.coreFold q) := by
  obtain ⟨y, rfl, hy⟩ := hq
  exact X.coreFold_oriented hy

theorem mdifferentiableAt_coreFold {q : X.Q.Carrier}
    (hq : ∃ y, X.capping.core y = q ∧ X.C.model.IsInteriorPoint y) :
    MDifferentiableAt X.Q.model W.model X.coreFold q := by
  obtain ⟨y, rfl, hy⟩ := hq
  exact (X.isLocalDiffeomorphAt_coreFold hy).mdifferentiableAt (by simp)

/-- **Positivity through the closed models.** A local diffeomorphism from the interior of a ball
chart of the closed model of a component to the closed model of `W` which near a point equals
`coreFold`, at the core image of an interior point, is orientation preserving there. -/
theorem orientation_map_of_eventuallyEq_coreFold [ConnectedSpace W.Carrier]
    (hW : W.model.boundary W.Carrier = ∅) (DQ : X.Q.Components)
    (hQ : ∀ i, (GC.Topology.componentCarrier X.Q DQ i).model.boundary
      (GC.Topology.componentCarrier X.Q DQ i).Carrier = ∅) {p : Fin DQ.count}
    (β : BallChart 3 (𝓡 3) (componentModel X.Q DQ hQ p).Carrier)
    (g : β.interior → (boundaryEmptyClosedModel W hW).Carrier) (x : β.interior)
    (hg : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ g x)
    (heq : g =ᶠ[𝓝 x] fun x' => X.coreFold (Subtype.val x'.val))
    (hx : ∃ y, X.capping.core y = Subtype.val x.val ∧ X.C.model.IsInteriorPoint y) :
    Orientation.map (Fin 3) (hg.mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
      ((componentModel X.Q DQ hQ p).orientation.orientation x.val) =
        (boundaryEmptyClosedModel W hW).orientation.orientation (g x) := by
  let Qp := GC.Topology.componentCarrier X.Q DQ p
  let _ := boundaryEmptyChartedSpace Qp (hQ p)
  have _ := boundaryEmptyIsManifold Qp (hQ p)
  let bQ : (componentModel X.Q DQ hQ p).Carrier ≃ₘ⟮𝓡 3, X.Q.model⟯ DQ.piece p :=
    (boundaryEmptyDiffeomorph Qp (hQ p)).symm
  have hbQ : bQ.preservesOrientation (componentModel X.Q DQ hQ p).orientation
      (X.Q.orientation.restrictOpen (DQ.piece p)) :=
    boundaryEmptyDiffeomorph_symm_preservesOrientation Qp (hQ p)
  let bW := boundaryEmptyClosedDiffeomorph W hW
  let G : β.interior → (boundaryEmptyClosedModel W hW).Carrier :=
    ⇑bW ∘ X.coreFold ∘ (Subtype.val : DQ.piece p → X.Q.Carrier) ∘ ⇑bQ ∘
      (Subtype.val : β.interior → (componentModel X.Q DQ hQ p).Carrier)
  have hG : G = fun x' => X.coreFold (Subtype.val x'.val) := by
    funext x'
    rfl
  have hGeq : g =ᶠ[𝓝 x] G := by
    rw [hG]
    exact heq
  have hpt : ((Subtype.val : DQ.piece p → X.Q.Carrier) ∘ ⇑bQ ∘
      (Subtype.val : β.interior → (componentModel X.Q DQ hQ p).Carrier)) x =
      (Subtype.val x.val : X.Q.Carrier) := rfl
  have hx' : ∃ y, X.capping.core y = ((Subtype.val : DQ.piece p → X.Q.Carrier) ∘ ⇑bQ ∘
      (Subtype.val : β.interior → (componentModel X.Q DQ hQ p).Carrier)) x ∧
      X.C.model.IsInteriorPoint y := by
    rw [hpt]
    exact hx
  have h1 := exists_orientation_map_subtype_val (I := 𝓡 3) β.interior x
    ((componentModel X.Q DQ hQ p).orientation.orientation x.val)
  have h2 := exists_orientation_map_of_preservesOrientation bQ hbQ x.val
  have h3 := exists_orientation_map_subtype_val (I := X.Q.model) (DQ.piece p) (bQ x.val)
    (X.Q.orientation.orientation (Subtype.val (bQ x.val)))
  have h4 := X.coreFold_oriented' hx'
  have h5 := exists_orientation_map_of_preservesOrientation bW
    (boundaryEmptyClosedDiffeomorph_preservesOrientation W hW)
    (X.coreFold (((Subtype.val : DQ.piece p → X.Q.Carrier) ∘ ⇑bQ ∘
      (Subtype.val : β.interior → (componentModel X.Q DQ hQ p).Carrier)) x))
  have hd1 : MDifferentiableAt (𝓡 3) (𝓡 3)
      (Subtype.val : β.interior → (componentModel X.Q DQ hQ p).Carrier) x :=
    (DifferentialGeometry.hasMFDerivAt_subtype_val β.interior x).mdifferentiableAt
  have hd2 : MDifferentiableAt (𝓡 3) X.Q.model bQ x.val := bQ.mdifferentiable (by simp) x.val
  have hd3 : MDifferentiableAt X.Q.model X.Q.model (Subtype.val : DQ.piece p → X.Q.Carrier)
      (bQ x.val) :=
    (DifferentialGeometry.hasMFDerivAt_subtype_val (DQ.piece p) (bQ x.val)).mdifferentiableAt
  have hd4 := X.mdifferentiableAt_coreFold hx'
  have hd5 : MDifferentiableAt W.model (𝓡 3) bW (X.coreFold
      (((Subtype.val : DQ.piece p → X.Q.Carrier) ∘ ⇑bQ ∘
        (Subtype.val : β.interior → (componentModel X.Q DQ hQ p).Carrier)) x)) :=
    bW.mdifferentiable (by simp) _
  have k12 := exists_orientation_map_comp hd1 hd2 h1 h2
  have k123 := exists_orientation_map_comp (hd2.comp x hd1) hd3 k12 h3
  have k1234 := exists_orientation_map_comp (hd3.comp x (hd2.comp x hd1)) hd4 k123 h4
  obtain ⟨L, hL, hoL⟩ :=
    exists_orientation_map_comp (hd4.comp x (hd3.comp x (hd2.comp x hd1))) hd5 k1234 h5
  have hd : mfderiv (𝓡 3) (𝓡 3) g x = mfderiv (𝓡 3) (𝓡 3) G x := hGeq.mfderiv_eq
  exact orientation_map_eq_of_point_eq hGeq.self_of_nhds _ L
    (fun v => (congrArg (fun T => T v) hd).trans (hL v).symm) _
    (boundaryEmptyClosedModel W hW).orientation.orientation hoL

end SphereCutCapped

end GC.GraphManifold.Assembly
