import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.HarmonicDensityReg
import DifferentialGeometry.Geometry.Curvature.Bochner.OrthonormalFrameTrace
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.RankZeroInner
import DifferentialGeometry.Geometry.Exponential.Smoothness.IntrinsicMfderivZero
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.InverseMetricRaisedEndomorphismJetBound
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Joint regularity of the finite-spectral Dirichlet density

The finite-spectral local addition is jointly `C^3` in the coefficient and
the spatial point.  Its spatial differential is therefore jointly `C^2`.
This file combines that fact with the smooth inverse-cometric coefficient and
the target metric to prove the corresponding joint `C^2` regularity of
`hmfDirDensity`.

The definition of `hmfDirDensity` uses a smooth orthonormal frame whose centre
is the evaluation point.  Such a moving-centre frame is not itself a smooth
field.  The proof consequently freezes the frame at the point under
consideration, proves regularity with that fixed smooth frame, and returns to
the moving-centre definition by the basis-independence of a genuine bilinear
trace.

The final section records the state-dependent mass pairing forced by the
local-addition parametrisation.  It is deliberately distinct from `hmfMass`:
away from the zero section, the coefficient velocity must first be pushed by
the state derivative of the exponential chart.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Tensor0SBundle Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators Matrix

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [T2Space M]
  [SigmaCompactSpace M] [BoundarylessManifold I M] [ConnectedSpace M]

/-! ## A jointly regular spatial pushforward -/

/-- The differential in the spatial slot of the finite-spectral local
addition, applied to a fixed smooth tangent field, is jointly `C^2` in the
coefficient and spatial variables.

The proof uses the parameterised `mfderivWithin` theorem for the genuinely
joint map `(u,x) ↦ hmfAdd q (hmfSpecIncl q S u) x`.  Thus the coefficient
dependence of the spatial derivative is retained; this is stronger than
applying the tangent-map theorem separately to each coefficient slice. -/
private theorem hmfSpecPush_cd
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (R : ℝ)
    (hmap : ContMDiffOn
      (𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I) I (3 : ℕ∞)
      (fun p : EuclideanSpace ℝ {i // i ∈ S} × M ↦
        hmfAdd (I := I) (M := M) q
          (hmfSpecIncl (I := I) (M := M) q S p.1) p.2)
      (Metric.ball 0 R ×ˢ (Set.univ : Set M)))
    (B : ∀ x : M, TangentSpace I x)
    (hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M ↦ (TotalSpace.mk' E x (B x) : TangentBundle I M))) :
    ContMDiffOn (𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I)
      (I.prod 𝓘(ℝ, E)) (2 : ℕ∞)
      (fun p : EuclideanSpace ℝ {i // i ∈ S} × M ↦
        (TotalSpace.mk' E
          (hmfAdd (I := I) (M := M) q
            (hmfSpecIncl (I := I) (M := M) q S p.1) p.2)
          (mfderiv I I
            (hmfAdd (I := I) (M := M) q
              (hmfSpecIncl (I := I) (M := M) q S p.1)) p.2 (B p.2)) :
          TangentBundle I M))
      (Metric.ball 0 R ×ˢ (Set.univ : Set M)) := by
  intro p hp
  let D : Set (EuclideanSpace ℝ {i // i ∈ S} × M) :=
    Metric.ball 0 R ×ˢ (Set.univ : Set M)
  let f : (EuclideanSpace ℝ {i // i ∈ S} × M) → M → M :=
    fun z y ↦ hmfAdd (I := I) (M := M) q
      (hmfSpecIncl (I := I) (M := M) q S z.1) y
  have hpD : p ∈ D := hp
  have hf : ContMDiffWithinAt
      ((𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I).prod I) I (3 : ℕ∞)
      (Function.uncurry f) (D ×ˢ (Set.univ : Set M)) (p, p.2) := by
    have hpre : ContMDiffWithinAt
        ((𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I).prod I)
        (𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I) (3 : ℕ∞)
        (fun z : (EuclideanSpace ℝ {i // i ∈ S} × M) × M ↦ (z.1.1, z.2))
        (D ×ˢ (Set.univ : Set M)) (p, p.2) :=
      (contMDiffWithinAt_fst.fst).prodMk contMDiffWithinAt_snd
    have hmaps : MapsTo
        (fun z : (EuclideanSpace ℝ {i // i ∈ S} × M) × M ↦ (z.1.1, z.2))
        (D ×ˢ (Set.univ : Set M)) D := by
      rintro ⟨z, y⟩ ⟨hz, -⟩
      exact ⟨hz.1, Set.mem_univ y⟩
    exact (hmap p hp).comp (p, p.2) hpre hmaps
  have hg : ContMDiffWithinAt
      (𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I) I (2 : ℕ∞)
      (fun z : EuclideanSpace ℝ {i // i ∈ S} × M ↦ z.2) D p :=
    contMDiffWithinAt_snd
  have hu : MapsTo
      (fun z : EuclideanSpace ℝ {i // i ∈ S} × M ↦ z.2) D
      (Set.univ : Set M) := fun _ _ ↦ Set.mem_univ _
  have hφ := ContMDiffWithinAt.mfderivWithin
    (I := I) (I' := I) (n := (3 : ℕ∞)) (m := (2 : ℕ∞))
    (f := f) (g := fun z : EuclideanSpace ℝ {i // i ∈ S} × M ↦ z.2)
    (t := D) (u := (Set.univ : Set M)) (x₀ := p)
    hf hg hpD hu (by norm_num) uniqueMDiffOn_univ
  have hv0 : ContMDiff
      (𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun z : EuclideanSpace ℝ {i // i ∈ S} × M ↦
        (TotalSpace.mk' E z.2 (B z.2) : TangentBundle I M)) :=
    hB.comp contMDiff_snd
  have hv : ContMDiffWithinAt
      (𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I) (I.prod 𝓘(ℝ, E))
      (2 : ℕ∞)
      (fun z : EuclideanSpace ℝ {i // i ∈ S} × M ↦
        (TotalSpace.mk' E z.2 (B z.2) : TangentBundle I M)) D p :=
    (hv0.of_le (by simp)).contMDiffAt.contMDiffWithinAt
  have hb₂ : ContMDiffWithinAt
      (𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I) I (2 : ℕ∞)
      (fun z : EuclideanSpace ℝ {i // i ∈ S} × M ↦ f z z.2) D p :=
    (hmap.of_le (by norm_num)) p hp
  have hkey := ContMDiffWithinAt.clm_apply_of_inCoordinates
    (IB₁ := I) (IB₂ := I) (F₁ := E) (F₂ := E)
    (E₁ := TangentSpace I (M := M)) (E₂ := TangentSpace I (M := M))
    (b₁ := fun z : EuclideanSpace ℝ {i // i ∈ S} × M ↦ z.2)
    (b₂ := fun z : EuclideanSpace ℝ {i // i ∈ S} × M ↦ f z z.2)
    (ϕ := fun z : EuclideanSpace ℝ {i // i ∈ S} × M ↦
      mfderiv I I (f z) z.2)
    (v := fun z : EuclideanSpace ℝ {i // i ∈ S} × M ↦ B z.2)
    (m₀ := p) (s := D) (n := (2 : ℕ∞))
    ?_ hv hb₂
  · convert hkey using 2
  · have hrw :
        (fun z : EuclideanSpace ℝ {i // i ∈ S} × M ↦
          ContinuousLinearMap.inCoordinates E (TangentSpace I (M := M))
            E (TangentSpace I (M := M))
            ((fun w : EuclideanSpace ℝ {i // i ∈ S} × M ↦ w.2) p)
            ((fun w : EuclideanSpace ℝ {i // i ∈ S} × M ↦ w.2) z)
            ((fun w : EuclideanSpace ℝ {i // i ∈ S} × M ↦ f w w.2) p)
            ((fun w : EuclideanSpace ℝ {i // i ∈ S} × M ↦ f w w.2) z)
            (mfderiv I I (f z) z.2)) =
          (fun z : EuclideanSpace ℝ {i // i ∈ S} × M ↦
            inTangentCoordinates I I
              (fun w : EuclideanSpace ℝ {i // i ∈ S} × M ↦ w.2)
              (fun w : EuclideanSpace ℝ {i // i ∈ S} × M ↦ f w w.2)
              (fun w : EuclideanSpace ℝ {i // i ∈ S} × M ↦
                mfderivWithin I I (f w) (Set.univ : Set M) w.2) p z) := by
      funext z
      rw [inTangentCoordinates, mfderivWithin_univ]
    rw [hrw]
    exact hφ

/-! ## Frozen-frame density -/

/-- Applying the inverse-cometric endomorphism to a frozen smooth
orthonormal-frame vector gives a smooth tangent section, jointly with an
unused finite-spectral parameter. -/
private theorem hmfRaisedFrame_cd
    (q h : SmoothRiemannianMetric I M)
    (x₀ : M) (i : Fin (Module.finrank ℝ E)) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M ↦ (TotalSpace.mk' E x
        (gInvRaisedEndo (I := I) q h x
          (smoothOrthoFrame (I := I) q x₀ i x)) : TangentBundle I M)) := by
  simpa only [fullRaisedEndoField_apply] using ContMDiff.clm_bundle_apply
    (b := id)
    (fullRaisedEndoField (I := I) (M := M) q h).contMDiff_toFun
    (smoothOrthoFrame_smooth (I := I) q x₀ i)

/-- With the orthonormal frame frozen at `x₀`, the finite-spectral
Dirichlet-density expression is jointly `C^2` on the coefficient ball. -/
private theorem hmfSpecFrozen_cd
    (q h : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (R : ℝ)
    (hmap : ContMDiffOn
      (𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I) I (3 : ℕ∞)
      (fun p : EuclideanSpace ℝ {i // i ∈ S} × M ↦
        hmfAdd (I := I) (M := M) q
          (hmfSpecIncl (I := I) (M := M) q S p.1) p.2)
      (Metric.ball 0 R ×ˢ (Set.univ : Set M)))
    (x₀ : M) :
    ContMDiffOn (𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I) 𝓘(ℝ)
      (2 : ℕ∞)
      (fun p : EuclideanSpace ℝ {i // i ∈ S} × M ↦
        (1 / 2 : ℝ) *
          ∑ i : Fin (Module.finrank ℝ E),
            q.inner
              (hmfAdd (I := I) (M := M) q
                (hmfSpecIncl (I := I) (M := M) q S p.1) p.2)
              (mfderiv I I
                (hmfAdd (I := I) (M := M) q
                  (hmfSpecIncl (I := I) (M := M) q S p.1)) p.2
                (gInvRaisedEndo (I := I) q h p.2
                  (smoothOrthoFrame (I := I) q x₀ i p.2)))
              (mfderiv I I
                (hmfAdd (I := I) (M := M) q
                  (hmfSpecIncl (I := I) (M := M) q S p.1)) p.2
                (smoothOrthoFrame (I := I) q x₀ i p.2)))
      (Metric.ball 0 R ×ˢ (Set.univ : Set M)) := by
  classical
  let D : Set (EuclideanSpace ℝ {i // i ∈ S} × M) :=
    Metric.ball 0 R ×ˢ (Set.univ : Set M)
  let F : EuclideanSpace ℝ {i // i ∈ S} × M → M :=
    fun p ↦ hmfAdd (I := I) (M := M) q
      (hmfSpecIncl (I := I) (M := M) q S p.1) p.2
  have hmetric : ContMDiffOn
      (𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) (2 : ℕ∞)
      (fun p : EuclideanSpace ℝ {i // i ∈ S} × M ↦
        TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) (F p) (q.inner (F p))) D := by
    simpa only [Function.comp_apply] using
      (q.contMDiff.of_le (by simp)).comp_contMDiffOn (hmap.of_le (by norm_num))
  have hterm : ∀ i : Fin (Module.finrank ℝ E),
      ContMDiffOn (𝓘(ℝ, EuclideanSpace ℝ {j // j ∈ S}).prod I) 𝓘(ℝ)
        (2 : ℕ∞)
        (fun p : EuclideanSpace ℝ {j // j ∈ S} × M ↦
          q.inner (F p)
            (mfderiv I I
              (hmfAdd (I := I) (M := M) q
                (hmfSpecIncl (I := I) (M := M) q S p.1)) p.2
              (gInvRaisedEndo (I := I) q h p.2
                (smoothOrthoFrame (I := I) q x₀ i p.2)))
            (mfderiv I I
              (hmfAdd (I := I) (M := M) q
                (hmfSpecIncl (I := I) (M := M) q S p.1)) p.2
              (smoothOrthoFrame (I := I) q x₀ i p.2))) D := by
    intro i
    have hframe : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M ↦ (TotalSpace.mk' E x
          (smoothOrthoFrame (I := I) q x₀ i x) : TangentBundle I M)) :=
      smoothOrthoFrame_smooth (I := I) q x₀ i
    have hraised := hmfRaisedFrame_cd (I := I) (M := M) q h x₀ i
    have hpush := hmfSpecPush_cd (I := I) (M := M) q S R hmap
      (fun x : M ↦ smoothOrthoFrame (I := I) q x₀ i x) hframe
    have hpushRaised := hmfSpecPush_cd (I := I) (M := M) q S R hmap
      (fun x : M ↦ gInvRaisedEndo (I := I) q h x
        (smoothOrthoFrame (I := I) q x₀ i x))
      hraised
    have happ := ContMDiffOn.clm_bundle_apply₂
      (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (b := F) hmetric hpushRaised hpush
    intro p hp
    have hat := happ p hp
    rw [Bundle.contMDiffWithinAt_totalSpace] at hat
    exact hat.2
  intro p hp
  have hc : ContMDiffWithinAt
      (𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I) 𝓘(ℝ) (2 : ℕ∞)
      (fun _ : EuclideanSpace ℝ {i // i ∈ S} × M ↦ (1 / 2 : ℝ)) D p :=
    contMDiffWithinAt_const
  exact hc.mul (ContMDiffWithinAt.sum (fun i _ ↦ hterm i p hp))

/-- The pointwise density computed in the moving-centre orthonormal frame is
equal, on the frozen frame's orthonormality neighbourhood, to the expression
computed in that frozen frame. -/
private theorem hmfDens_eq_frozen
    (q h : SmoothRiemannianMetric I M) (Φ : M → M)
    (x₀ : M) {y : M}
    (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x₀) :
    hmfDirDensity (I := I) (M := M) q h Φ y =
      (1 / 2 : ℝ) *
        ∑ i : Fin (Module.finrank ℝ E),
          q.inner (Φ y)
            (mfderiv I I Φ y
              (gInvRaisedEndo (I := I) q h y
                (smoothOrthoFrame (I := I) q x₀ i y)))
            (mfderiv I I Φ y
              (smoothOrthoFrame (I := I) q x₀ i y)) := by
  classical
  let dΦ : TangentSpace I y →L[ℝ] TangentSpace I (Φ y) := mfderiv I I Φ y
  let A : TangentSpace I y →L[ℝ] TangentSpace I y :=
    gInvRaisedEndo (I := I) q h y
  let step₁ : TangentSpace I y →L[ℝ] TangentSpace I (Φ y) →L[ℝ] ℝ :=
    (q.inner (Φ y)).comp (dΦ.comp A)
  let precomp : (TangentSpace I (Φ y) →L[ℝ] ℝ) →L[ℝ]
      (TangentSpace I y →L[ℝ] ℝ) := ContinuousLinearMap.precomp ℝ dΦ
  let Hb : TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ :=
    precomp.comp step₁
  have hmove := orthonormal_basis_bilin_trace (I := I) (M := M) q y Hb
    (fun i ↦ smoothOrthoFrame (I := I) q y i y)
    (fun i j ↦ smoothOrthoFrame_orthonormal_at_center (I := I) q y i j)
  have hfixed := orthonormal_basis_bilin_trace (I := I) (M := M) q y Hb
    (fun i ↦ smoothOrthoFrame (I := I) q x₀ i y)
    (fun i j ↦ smoothOrthoFrame_orthonormal (I := I) q x₀ hy i j)
  unfold hmfDirDensity
  exact congrArg (fun z : ℝ ↦ (1 / 2 : ℝ) * z) (by
    simpa only [Hb, precomp, step₁, dΦ, A, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.precomp_apply] using hmove.trans hfixed.symm)

/-! ## The moving-centre density -/

/-- On one coefficient ball, the finite-spectral Dirichlet density is jointly
`C^2` in the coefficient and spatial variables.  The radius is uniform in the
spatial point and is exactly the radius on which the local-addition map is
jointly `C^3`. -/
theorem hmfSpecDens_cd
    (q h : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1)) :
    ∃ R : ℝ, 0 < R ∧
      ContMDiffOn (𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I) 𝓘(ℝ)
        (2 : ℕ∞)
        (fun p : EuclideanSpace ℝ {i // i ∈ S} × M ↦
          hmfDirDensity (I := I) (M := M) q h
            (hmfAdd (I := I) (M := M) q
              (hmfSpecIncl (I := I) (M := M) q S p.1)) p.2)
        (Metric.ball 0 R ×ˢ (Set.univ : Set M)) := by
  obtain ⟨R, hR, hmap⟩ := hmfSpecMap_cd (I := I) (M := M) q S 3 (by norm_num)
  refine ⟨R, hR, ?_⟩
  intro p hp
  have hfrozen := hmfSpecFrozen_cd (I := I) (M := M) q h S R hmap p.2 p hp
  refine hfrozen.congr_of_eventuallyEq_of_mem ?_ hp
  have hnbhd : ∀ᶠ z : EuclideanSpace ℝ {i // i ∈ S} × M in
      𝓝[Metric.ball 0 R ×ˢ (Set.univ : Set M)] p,
      z.2 ∈ smoothOrthoFrameNbhd (I := I) (M := M) p.2 := by
    apply Filter.Eventually.filter_mono inf_le_left
    exact continuousAt_snd.eventually
      (smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) p.2)
  filter_upwards [hnbhd] with z hz
  exact hmfDens_eq_frozen (I := I) (M := M) q h
    (hmfAdd (I := I) (M := M) q
      (hmfSpecIncl (I := I) (M := M) q S z.1)) p.2 hz

/-! ## The jointly regular coefficient derivative -/

/-- For a fixed finite coefficient direction, the derivative of the
local-addition map in that coefficient direction is a jointly `C^2`
tangent-bundle section on one coefficient ball.  The radius is the same
uniform-in-space radius delivered by the joint `C^3` local-addition theorem.

This is the bundled regularity needed for the two pushed coefficient
directions in the faithful finite mass. -/
theorem hmfSpecCoeff_cd
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (v : EuclideanSpace ℝ {i // i ∈ S}) :
    ∃ R : ℝ, 0 < R ∧
      ContMDiffOn (𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I)
        (I.prod 𝓘(ℝ, E)) (2 : ℕ∞)
        (fun p : EuclideanSpace ℝ {i // i ∈ S} × M ↦
          (TotalSpace.mk' E
            (hmfAdd (I := I) (M := M) q
              (hmfSpecIncl (I := I) (M := M) q S p.1) p.2)
            (mfderiv 𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}) I
              (fun u : EuclideanSpace ℝ {i // i ∈ S} ↦
                hmfAdd (I := I) (M := M) q
                  (hmfSpecIncl (I := I) (M := M) q S u) p.2)
              p.1 v) : TangentBundle I M))
        (Metric.ball 0 R ×ˢ (Set.univ : Set M)) := by
  obtain ⟨R, hR, hmap⟩ :=
    hmfSpecMap_cd (I := I) (M := M) q S 3 (by norm_num)
  refine ⟨R, hR, ?_⟩
  intro p hp
  let V := EuclideanSpace ℝ {i // i ∈ S}
  let IV : ModelWithCorners ℝ V V := 𝓘(ℝ, V)
  let P : ModelWithCorners ℝ (V × E) (V × H) := IV.prod I
  let F : V × M → M := fun z ↦
    hmfAdd (I := I) (M := M) q
      (hmfSpecIncl (I := I) (M := M) q S z.1) z.2
  let f : (V × M) → V → M := fun z u ↦
    hmfAdd (I := I) (M := M) q
      (hmfSpecIncl (I := I) (M := M) q S u) z.2
  have hopen : IsOpen (Metric.ball (0 : V) R ×ˢ (Set.univ : Set M)) :=
    Metric.isOpen_ball.prod isOpen_univ
  have hmapAt : ContMDiffAt P I (3 : ℕ∞) F p := by
    exact (hmap p hp).contMDiffAt (hopen.mem_nhds hp)
  have hf : ContMDiffAt (P.prod IV) I (3 : ℕ∞)
      (Function.uncurry f) (p, p.1) := by
    have hpre : ContMDiffAt (P.prod IV) P (3 : ℕ∞)
        (fun z : (V × M) × V ↦ (z.2, z.1.2)) (p, p.1) :=
      contMDiffAt_snd.prodMk (contMDiffAt_fst.snd)
    simpa only [Function.uncurry_apply_pair, f, F] using
      hmapAt.comp (p, p.1) hpre
  have hg : ContMDiffAt P IV (2 : ℕ∞)
      (fun z : V × M ↦ z.1) p := contMDiffAt_fst
  have hφ := ContMDiffAt.mfderiv
    (I := IV) (I' := I) (n := (3 : ℕ∞)) (m := (2 : ℕ∞))
    (f := f) (g := fun z : V × M ↦ z.1) hf hg (by norm_num)
  have hv0 : ContMDiff IV (IV.tangent) ∞
      (fun u : V ↦ (TotalSpace.mk' V u v : TangentBundle IV V)) :=
    (contMDiff_vectorSpace_iff_contDiff (V := fun _ : V ↦ v)).mpr
      contDiff_const
  have hv : ContMDiffAt P (IV.prod 𝓘(ℝ, V)) (2 : ℕ∞)
      (fun z : V × M ↦
        (TotalSpace.mk' V z.1 v : TangentBundle IV V)) p := by
    exact (hv0.of_le (by simp)).contMDiffAt.comp p contMDiffAt_fst
  have hb₂ : ContMDiffAt P I (2 : ℕ∞) F p :=
    hmapAt.of_le (by norm_num)
  have hkey := ContMDiffAt.clm_apply_of_inCoordinates
    (IB₁ := IV) (IB₂ := I) (F₁ := V) (F₂ := E)
    (E₁ := TangentSpace IV (M := V))
    (E₂ := TangentSpace I (M := M))
    (b₁ := fun z : V × M ↦ z.1) (b₂ := F)
    (ϕ := fun z : V × M ↦ mfderiv IV I (f z) z.1)
    (v := fun _ : V × M ↦ v) (m₀ := p) (n := (2 : ℕ∞))
    ?_ hv hb₂
  · convert hkey.contMDiffWithinAt using 2
  · have hrw :
        (fun z : V × M ↦
          ContinuousLinearMap.inCoordinates V (TangentSpace IV (M := V))
            E (TangentSpace I (M := M))
            ((fun w : V × M ↦ w.1) p) ((fun w : V × M ↦ w.1) z)
            (F p) (F z) (mfderiv IV I (f z) z.1)) =
          (fun z : V × M ↦
            inTangentCoordinates IV I (fun w : V × M ↦ w.1)
              (fun w : V × M ↦ f w w.1)
              (fun w : V × M ↦ mfderiv IV I (f w) w.1) p z) := by
      funext z
      rw [inTangentCoordinates]
    rw [hrw]
    exact hφ

/-! ## The faithful state-dependent mass -/

/-- Pointwise variation of the local-addition state `S` in the smooth-tensor
direction `U`.  A one-dimensional line is used so that no artificial Banach
topology on the full space of smooth sections is introduced. -/
noncomputable def hmfStateVar
    (q : SmoothRiemannianMetric I M)
    (S U : SmoothCcTensor q 0 1) (x : M) :
    TangentSpace I (hmfAdd (I := I) (M := M) q S x) :=
  mfderiv 𝓘(ℝ) I
    (fun a : ℝ ↦ hmfAdd (I := I) (M := M) q (S + a • U) x) 0 1

/-- State-dependent mass pairing in local-addition coordinates.  Unlike
`hmfMass`, both coefficient directions are pushed through the state
derivative of the exponential chart before being paired by the target
metric. -/
noncomputable def hmfStateMass
    (q h : SmoothRiemannianMetric I M)
    (S U V : SmoothCcTensor q 0 1) : ℝ :=
  ∫ x, q.inner (hmfAdd (I := I) (M := M) q S x)
      (hmfStateVar (I := I) (M := M) q S U x)
      (hmfStateVar (I := I) (M := M) q S V x)
    ∂(riemannianVolumeMeasure (I := I) (M := M) h)

/-! ### The zero-section state derivative -/

/-- The fixed-base exponential hidden in `hmfDiagExp`.  Keeping this small
wrapper separate makes the one-dimensional state derivative a literal
composition with a map on the fixed model fibre. -/
private noncomputable def hmfFiberExp
    (q : SmoothRiemannianMetric I M) (x : M) : E → M :=
  fun v : E ↦
    (hmfDiagExp (I := I) (M := M) q
      (⟨x, (show TangentSpace I x from v)⟩ : TangentBundle I M)).2

/-- The derivative of the fixed-base HMF exponential at the zero tangent
vector is the identity.  The local metric instances duplicate the concrete
instances hidden inside `hmfDiagExp`; no global Riemannian-bundle instance is
introduced. -/
private theorem hmfFiberExp_mfd
    (q : SmoothRiemannianMetric I M) (x : M) :
    mfderiv 𝓘(ℝ, E) I (hmfFiberExp (I := I) (M := M) q x) 0 =
      ContinuousLinearMap.id ℝ E := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
    ⟨q.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun y : M ↦ TangentSpace I y) :=
    ⟨q.inner, q.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  letI : PseudoEMetricSpace M :=
    PseudoEMetricSpace.ofRiemannianMetric I M
  have hEnorm : ∀ (y : M) (v : TangentSpace I y),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (q.inner y v v)) := by
    intro y v
    rw [← ofReal_norm_eq_enorm, norm_eq_sqrt_real_inner]
    rfl
  simpa only [hmfFiberExp, hmfDiagExp, diagExp_snd] using
    (mfderiv_expMapIntrinsic_at_zero (I := I) q hEnorm x)

/-- The fixed-base HMF exponential is manifold differentiable at the zero
tangent vector.  This follows from its already identified nonzero derivative:
if differentiability failed, `mfderiv` would be the zero map. -/
private theorem hmfFiberExp_md
    (q : SmoothRiemannianMetric I M) (x : M) :
    MDifferentiableAt 𝓘(ℝ, E) I
      (hmfFiberExp (I := I) (M := M) q x) 0 := by
  haveI : Nontrivial E :=
    Module.nontrivial_of_finrank_pos
      (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  by_contra hnot
  have hzero := hmfFiberExp_mfd (I := I) (M := M) q x
  rw [mfderiv_zero_of_not_mdifferentiableAt hnot] at hzero
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hv' : (0 : E) = v := by
    simpa using DFunLike.congr_fun hzero v
  exact hv hv'.symm

/-- At the zero state, the derivative of the exponential local-addition
coordinate in a smooth tensor direction is exactly the raised one-form field
represented by that tensor. -/
@[simp] theorem hmfStateVar_zero
    (q : SmoothRiemannianMetric I M)
    (U : SmoothCcTensor q 0 1) (x : M) :
    hmfStateVar (I := I) (M := M) q 0 U x =
      hmfUnknown (I := I) q U x := by
  let w : E := hmfUnknown (I := I) q U x
  let line : ℝ → E := fun a : ℝ ↦ a • w
  have hpath :
      (fun a : ℝ ↦ hmfAdd (I := I) (M := M) q
        ((0 : SmoothCcTensor q 0 1) + a • U) x) =
        hmfFiberExp (I := I) (M := M) q x ∘ line := by
    funext a
    simp only [zero_add, Function.comp_apply, line, w, hmfFiberExp,
      hmfAdd, hmfUnknown_smul]
  have hline_md : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, E) line 0 := by
    have hMD : ContMDiff 𝓘(ℝ) 𝓘(ℝ, E) ∞ line := by
      simpa only [line] using contMDiff_id.smul contMDiff_const
    exact hMD.contMDiffAt.mdifferentiableAt (by decide)
  have hline : mfderiv 𝓘(ℝ) 𝓘(ℝ, E) line 0 (1 : ℝ) = w := by
    rw [mfderiv_eq_fderiv]
    have h : HasFDerivAt line
        ((1 : ℝ →L[ℝ] ℝ).smulRight w) 0 := by
      simpa only [line] using (hasFDerivAt_id (0 : ℝ)).smul_const w
    rw [h.fderiv]
    simp only [ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.one_apply, one_smul]
  have houter : MDifferentiableAt 𝓘(ℝ, E) I
      (hmfFiberExp (I := I) (M := M) q x) (line 0) := by
    simpa only [line, zero_smul] using
      hmfFiberExp_md (I := I) (M := M) q x
  unfold hmfStateVar
  rw [hpath]
  calc
    mfderiv 𝓘(ℝ) I
        (hmfFiberExp (I := I) (M := M) q x ∘ line) 0 (1 : ℝ) =
        mfderiv 𝓘(ℝ, E) I
          (hmfFiberExp (I := I) (M := M) q x) (line 0)
          (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) line 0 (1 : ℝ)) :=
      mfderiv_comp_apply (f := line) (x := (0 : ℝ))
        houter hline_md (1 : ℝ)
    _ = hmfUnknown (I := I) q U x := by
      rw [hline]
      simp only [line, zero_smul]
      rw [hmfFiberExp_mfd]
      rfl

/-! ### The rank-one mass bridge -/

/-- Every upper-rank-zero mixed tensor is the canonical rank-zero lift of
its value on the unit scalar tensor. -/
private theorem hmfUnitLift
    (q : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor q 0 1) (x : M) :
    Tensor0SSpace.toRS0
        (unitEvalSection (I := I) (M := M) q 1 S x) =
      S.toSection x := by
  apply tensorRSSpace_ext (I := I) (M := M) 0 1 x
  intro c
  have hc : c = tensor0SSpace_evalScalar x c •
      unitZeroSec (I := I) (M := M) x := by
    apply Tensor0SSpace.toModel_injective
    apply ContinuousMultilinearMap.ext
    intro v
    change Tensor0SSpace.toModel c v =
      Tensor0SSpace.toModel
        (tensor0SSpace_evalScalar x c •
          unitZeroSec (I := I) (M := M) x) v
    rw [Tensor0SSpace.toModel_smul,
      ContinuousMultilinearMap.smul_apply, unitZeroSec_apply,
      Tensor0SSpace.toModel_ofModel,
      ContinuousMultilinearMap.constOfIsEmpty_apply, smul_eq_mul,
      Tensor0SSpace.evalScalar_apply, mul_one]
    exact congrArg (Tensor0SSpace.toModel c)
      (Subsingleton.elim v Fin.elim0)
  rw [Tensor0SSpace.toRS0_apply, unitEvalSection_apply]
  calc
    tensor0SSpace_evalScalar x c •
          (S.toSection x) (unitZeroSec (I := I) (M := M) x) =
        (S.toSection x)
          (tensor0SSpace_evalScalar x c •
            unitZeroSec (I := I) (M := M) x) := by
      rw [map_smul]
    _ = (S.toSection x) c := congrArg (S.toSection x) hc.symm

/-- The inverse Gram matrix on the fixed model basis is a genuine inverse
metric in that basis. -/
private theorem hmfChartInv
    (q : SmoothRiemannianMetric I M) (x : M) :
    MetricInverseInBasis (I := I) q x (chartModelBasis E)
      (fun i j ↦ (gramMatrixAt (I := I) (M := M) q x)⁻¹ i j) := by
  classical
  have hdet : IsUnit (gramMatrixAt (I := I) (M := M) q x).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      (gramMatrixAt_isUnit (I := I) (M := M) q x)
  intro i j
  constructor
  · have hij := congrFun (congrFun
      (gramMatrixAt_inv_mul_self (I := I) (M := M) q x) i) j
    simpa only [Matrix.mul_apply, gramMatrixAt_apply, Matrix.one_apply] using hij
  · have hmul : gramMatrixAt (I := I) (M := M) q x *
        (gramMatrixAt (I := I) (M := M) q x)⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ hdet
    have hij := congrFun (congrFun hmul i) j
    simpa only [Matrix.mul_apply, gramMatrixAt_apply, Matrix.one_apply] using hij

/-- For one-forms, the recursively defined Gram-matrix tensor pairing is the
target-metric pairing of their musical sharps. -/
private theorem hmfCovInner
    (q : SmoothRiemannianMetric I M) (x : M)
    (α β : Tensor0SSpace 1 I x) :
    q.inner x
        (inverseMetricSharpFib (I := I) q x α)
        (inverseMetricSharpFib (I := I) q x β) =
      tensorInnerPointwise_0s (I := I) (M := M) 1 q x
        (Tensor0SSpace.toModel α) (Tensor0SSpace.toModel β) := by
  classical
  have hsharp : ∀ γ : Tensor0SSpace 1 I x,
      inverseMetricSharpFib (I := I) q x γ =
        cotangentSharp (I := I) q x γ := by
    intro γ
    apply metricFlatLinear_injective (I := I) q x
    ext w
    change q.inner x (inverseMetricSharpFib (I := I) q x γ) w =
      q.inner x (cotangentSharp (I := I) q x γ) w
    rw [inverseMetricSharpFib_inner, cotangentSharp_inner,
      cotangentToDualLinear_apply]
  have hcoord := cotangentInner_eq_coord (I := I) q x
    (chartModelBasis E)
    (fun i j ↦ (gramMatrixAt (I := I) (M := M) q x)⁻¹ i j)
    (hmfChartInv (I := I) (M := M) q x) α β
  have htensor :
      tensorInnerPointwise_0s (I := I) (M := M) 1 q x
          (Tensor0SSpace.toModel α) (Tensor0SSpace.toModel β) =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            (gramMatrixAt (I := I) (M := M) q x)⁻¹ i j *
              cotangentToDual (I := I) α ((chartModelBasis E) i) *
                cotangentToDual (I := I) β ((chartModelBasis E) j) := by
    rw [tensorInnerPointwise_0s_succ]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [tensorInnerPointwise_0s_zero_arity]
    have hα :
        ((Tensor0SSpace.toModel α).curryLeft ((chartModelBasis E) i))
            (fun k : Fin 0 ↦ Fin.elim0 k) =
          cotangentToDual (I := I) α ((chartModelBasis E) i) := by
      rw [ContinuousMultilinearMap.curryLeft_apply,
        cotangentToDual_apply]
      congr 1
      funext k
      fin_cases k
      rfl
    have hβ :
        ((Tensor0SSpace.toModel β).curryLeft ((chartModelBasis E) j))
            (fun k : Fin 0 ↦ Fin.elim0 k) =
          cotangentToDual (I := I) β ((chartModelBasis E) j) := by
      rw [ContinuousMultilinearMap.curryLeft_apply,
        cotangentToDual_apply]
      congr 1
      funext k
      fin_cases k
      rfl
    rw [hα, hβ]
    ring
  calc
    q.inner x
        (inverseMetricSharpFib (I := I) q x α)
        (inverseMetricSharpFib (I := I) q x β) =
        cotangentInner (I := I) q x α β := by
      rw [hsharp α, hsharp β]
      rfl
    _ = ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            (gramMatrixAt (I := I) (M := M) q x)⁻¹ i j *
              cotangentToDual (I := I) α ((chartModelBasis E) i) *
                cotangentToDual (I := I) β ((chartModelBasis E) j) := hcoord
    _ = tensorInnerPointwise_0s (I := I) (M := M) 1 q x
          (Tensor0SSpace.toModel α) (Tensor0SSpace.toModel β) := htensor.symm

/-- Pointwise, the target pairing of the raised HMF one-forms is exactly the
mixed-tensor pairing used by `hmfMass`. -/
private theorem hmfMassPt
    (q : SmoothRiemannianMetric I M)
    (U V : SmoothCcTensor q 0 1) (x : M) :
    q.inner x (hmfUnknown (I := I) q U x)
        (hmfUnknown (I := I) q V x) =
      tensorInnerPointwise (I := I) (M := M) q 0 1 x
        (U.toFun x) (V.toFun x) := by
  let α : Tensor0SSpace 1 I x :=
    unitEvalSection (I := I) (M := M) q 1 U x
  let β : Tensor0SSpace 1 I x :=
    unitEvalSection (I := I) (M := M) q 1 V x
  have hU : U.toFun x = TensorRSSpace.toModel
      (Tensor0SSpace.toRS0 α) := by
    rw [SmoothCcTensor.toFun_apply,
      hmfUnitLift (I := I) (M := M) q U x]
  have hV : V.toFun x = TensorRSSpace.toModel
      (Tensor0SSpace.toRS0 β) := by
    rw [SmoothCcTensor.toFun_apply,
      hmfUnitLift (I := I) (M := M) q V x]
  unfold hmfUnknown
  change q.inner x
      (inverseMetricSharpFib (I := I) q x α)
      (inverseMetricSharpFib (I := I) q x β) = _
  rw [hU, hV, inner_toRS0]
  exact hmfCovInner (I := I) (M := M) q x α β

/-- At the zero state, the faithful state-dependent mass is exactly the
older fixed-coordinate mass pairing. -/
@[simp] theorem hmfStateMass_zero_eq
    (q h : SmoothRiemannianMetric I M)
    (U V : SmoothCcTensor q 0 1) :
    hmfStateMass (I := I) (M := M) q h 0 U V =
      hmfMass (I := I) (M := M) q h U V := by
  unfold hmfStateMass hmfMass
  simp only [hmfAdd_zero, id_eq, hmfStateVar_zero]
  apply integral_congr_ae
  filter_upwards with x
  exact hmfMassPt (I := I) (M := M) q U V x

end DifferentialGeometry.PDE.RicciFlow.Pullback

end
