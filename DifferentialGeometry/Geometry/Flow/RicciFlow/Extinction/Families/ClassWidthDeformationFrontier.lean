import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.Deformation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.EssentialClass

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open Surgery.Topology Width CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
    [SigmaCompactSpace Q] [hT2 : T2Space Q] [hCompact : CompactSpace Q]
    [hConnected : ConnectedSpace Q] [hBoundary : I.Boundaryless]
    {D : RealTimeInterval} {a b : ℝ}

def ClassWidthDeformationFrontier (B : RicciBackground (I := I) (M := Q) D a b)
    (Γ : RegularFamily (I := I) (Q := Q) (Sphere 2)) (epsilon : ℝ) : Prop :=
  ∃ (d : ℕ) (e : SmoothLoopEmbedding (I := I) (Q := Q) d),
    ∀ ell : ℝ, 0 < ell →
      ∃ deformed : C(Icc a b, RegularFamily (I := I) (Q := Q) (Sphere 2)),
        (∀ t : Icc a b, HasContinuousSmoothLoopJets e (deformed t) ∧
          FreeHomotopyClass.mk (contractibleRegularLoopInclusion.comp (deformed t)) =
            FreeHomotopyClass.mk (contractibleRegularLoopInclusion.comp Γ)) ∧
        ∀ p : Sphere 2,
          loopLength (B.family.metric b)
            (((deformed ⟨b, B.lt.le, le_rfl⟩) p).1.toContinuousLoop) < ell ∨
          regularLeastArea (B.family.metric b) ((deformed ⟨b, B.lt.le, le_rfl⟩) p) ≤
            affineComparison B.family a b (regularLeastArea (B.family.metric a) (Γ p)) + epsilon

omit [SigmaCompactSpace Q] in
theorem classWidth_le_affineComparison_of_classWidthDeformationFrontier
    (B : RicciBackground (I := I) (M := Q) D a b)
    (ξ : FreeContractibleSphereClass Q) (hessential : IsEssentialFamilyClass ξ)
    (Γ : Width.RegularRepresentative (I := I) ξ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hfrontier : ClassWidthDeformationFrontier (I := I) (Q := Q) (D := D) (a := a) (b := b)
      B Γ.1 epsilon) :
    Width.classWidth (B.family.metric b) ξ ≤
      affineComparison B.family a b (Width.familyMaximum (B.family.metric a) Γ.1) +
        2 * epsilon := by
  classical
  obtain ⟨_d, _e, hdata⟩ := hfrontier
  obtain ⟨sigma, K, hsigma, hK, hlong, hshort⟩ :=
    rfs_essential_short_family (B.family.metric b)
  let ell := min sigma (min 1 (epsilon / (K + 1)))
  have hell : 0 < ell := lt_min hsigma (lt_min (by norm_num) (div_pos hepsilon (by positivity)))
  have hellsigma : ell ≤ sigma := min_le_left _ _
  have hellone : ell ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have helldiv : ell ≤ epsilon / (K + 1) := (min_le_right _ _).trans (min_le_right _ _)
  have hsmall : K * ell ^ 2 ≤ epsilon := by
    have hprod : ell * (K + 1) ≤ epsilon := (le_div_iff₀ (by positivity)).mp helldiv
    have hsquare : ell ^ 2 ≤ ell := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hsquare hK
    nlinarith
  obtain ⟨deformed, hclass, halt⟩ := hdata ell hell
  let tb : Icc a b := ⟨b, B.lt.le, le_rfl⟩
  let Γb : Width.RegularRepresentative (I := I) ξ :=
    ⟨deformed tb, (hclass tb).2.trans Γ.2⟩
  have hmono (p : Sphere 2) :
      affineComparison B.family a b (Width.regularLeastArea (B.family.metric a) (Γ.1 p)) ≤
        affineComparison B.family a b (Width.familyMaximum (B.family.metric a) Γ.1) :=
    (affineComparison_strictMono B.family a b).monotone
      (Width.regularLeastArea_le_familyMaximum (B.family.metric a) Γ.1 p)
  obtain ⟨p, hp⟩ := hlong ξ hessential Γb ell hell hellsigma
  have hnonneg : 0 ≤
      affineComparison B.family a b (Width.familyMaximum (B.family.metric a) Γ.1) + epsilon := by
    rcases halt p with hshortp | hlongp
    · exact False.elim ((not_lt_of_ge hp) hshortp)
    · have harea := Width.regularLeastArea_nonneg (B.family.metric b) (Γb.1 p)
      have hm := hmono p
      dsimp only [Γb, tb] at harea
      linarith
  have hmax : Width.familyMaximum (B.family.metric b) Γb.1 ≤
      affineComparison B.family a b (Width.familyMaximum (B.family.metric a) Γ.1) +
        2 * epsilon := by
    obtain ⟨q, hq⟩ := Width.familyMaximum_attained (B.family.metric b) Γb.1
    rw [hq]
    rcases halt q with hshortq | hlongq
    · have harea := (hshort (Γb.1 q) ell hell hellsigma hshortq).trans hsmall
      linarith
    · have hm := hmono q
      change Width.regularLeastArea (B.family.metric b)
        ((deformed ⟨b, B.lt.le, le_rfl⟩) q) ≤ _
      linarith
  exact (Width.classWidth_le_familyMaximum (B.family.metric b) ξ Γb).trans hmax

omit [SigmaCompactSpace Q] hBoundary in
theorem classWidthDeformationFrontier_of_preparedFamilyData
    (B : RicciBackground (I := I) (M := Q) D a b) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (Γ : RegularFamily (I := I) (Q := Q) (Sphere 2))
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (L₀ Theta₀ Ainit : ℝ) (hL₀ : 0 ≤ L₀) (hTheta₀ : 0 ≤ Theta₀)
    (hAinit : 0 ≤ Ainit)
    (hprepared : PreparedFamilyApproximation (I := I) (Q := Q) (D := D) (a := a) (b := b)
      B e Γ L₀ Theta₀ Ainit)
    (hflow : PreparedFamilyFlowData (I := I) (Q := Q) (D := D) (a := a) (b := b)
      B e L₀ Theta₀)
    (halt : ∀ ell : ℝ,
      RampAlternativeData (I := I) (Q := Q) (D := D) (a := a) (b := b) B ell epsilon) :
    ClassWidthDeformationFrontier (I := I) (Q := Q) (D := D) (a := a) (b := b) B Γ epsilon := by
  refine ⟨d, e, fun ell _ => ?_⟩
  obtain ⟨-, -, -, -, deformed, -, -, -, hclass, -, hfinal⟩ :=
    rfs_family_deformation_of_frontier B e Γ epsilon ell hepsilon L₀ Theta₀ Ainit hL₀
      hTheta₀ hAinit hprepared hflow (halt ell)
  exact ⟨deformed, hclass, hfinal⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
