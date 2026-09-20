import DifferentialGeometry.Geometry.Connection.ParallelTransport.Naturality.PullbackLocalIso
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.CovariantDerivativeDifference
import DifferentialGeometry.Topology.Manifold.CurveExtension


noncomputable section

namespace DifferentialGeometry.Geometry.Connection

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open scoped Manifold ContDiff Topology

variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]

theorem connectionDifference_map_of_local_isometry_on
    (g₁ g₂ : SmoothRiemannianMetric I M) (h₁ h₂ : SmoothRiemannianMetric J N)
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : IsLocalDiffeomorphOn I J ∞ f U)
    (hmetric₁ : ∀ (x : M), x ∈ U → ∀ v w : TangentSpace I x,
      g₁.inner x v w = h₁.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w))
    (hmetric₂ : ∀ (x : M), x ∈ U → ∀ v w : TangentSpace I x,
      g₂.inner x v w = h₂.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w))
    {x : M} (hx : x ∈ U) (u w : TangentSpace I x) :
    mfderiv I J f x (CovariantDerivative.difference (metricCov g₁) (metricCov g₂) x u w) =
      CovariantDerivative.difference (metricCov h₁) (metricCov h₂) (f x)
        (mfderiv I J f x u) (mfderiv I J f x w) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : CompleteSpace F := FiniteDimensional.complete ℝ F
  obtain ⟨gamma, hgamma, _hrange, hjet⟩ :=
    exists_contMDiff_curve_with_velocity_range_subset
      (I := I) (BoundarylessManifold.isInteriorPoint (I := I)) w (hU.mem_nhds hx)
  change (⟨gamma 0, mfderiv 𝓘(ℝ, ℝ) I gamma 0 1⟩ : TangentBundle I M) = ⟨x, w⟩ at hjet
  have hgamma₀ : gamma 0 = x := congrArg TotalSpace.proj hjet
  have hvelocity : (mfderiv 𝓘(ℝ, ℝ) I gamma 0 1 : E) = w :=
    congrArg (fun p : TangentBundle I M ↦ (p.2 : E)) hjet
  subst x
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) (gamma 0) u
  let V : ∀ s, TangentSpace I (gamma s) := fun s ↦ Y (gamma s)
  have hV : DifferentiableAt ℝ (chartRepAt (I := I) gamma V 0) 0 :=
    chartRepAt_restrict_differentiableAt
      (hgamma.of_le (WithTop.coe_le_coe.mpr (le_top : (1 : ℕ∞) ≤ ⊤))) Y
      (Y.contMDiff.of_le (WithTop.coe_le_coe.mpr (le_top : (1 : ℕ∞) ≤ ⊤))) 0
  have hgammaU : gamma 0 ∈ U := hx
  have hnat₁ := covDerivAlong_map_of_local_isometry_on g₁ h₁ hU hf hmetric₁
    gamma V hgammaU hgamma.contMDiffAt hV
  have hnat₂ := covDerivAlong_map_of_local_isometry_on g₂ h₂ hU hf hmetric₂
    gamma V hgammaU hgamma.contMDiffAt hV
  have hdiff := congrArg₂ (fun a b : F ↦ a - b) hnat₁ hnat₂
  have hgammaD : MDifferentiableAt 𝓘(ℝ, ℝ) I gamma 0 :=
    hgamma.mdifferentiableAt (by simp)
  have hfD : MDifferentiableAt I J f (gamma 0) :=
    (hf ⟨gamma 0, hgammaU⟩).mdifferentiableAt (by simp)
  have htargetD : MDifferentiableAt 𝓘(ℝ, ℝ) J (fun s ↦ f (gamma s)) 0 :=
    hfD.comp 0 hgammaD
  have hchain := mfderiv_comp_apply 0 hfD hgammaD (1 : ℝ)
  have hraw : (mfderiv I J f (gamma 0)
      (covDerivAlong g₁ gamma V 0 - covDerivAlong g₂ gamma V 0) : F) =
      covDerivAlong h₁ (fun s ↦ f (gamma s))
        (fun s ↦ mfderiv I J f (gamma s) (V s)) 0 -
      covDerivAlong h₂ (fun s ↦ f (gamma s))
        (fun s ↦ mfderiv I J f (gamma s) (V s)) 0 :=
    ((mfderiv I J f (gamma 0)).map_sub _ _).trans hdiff
  have hsource := covAlong_diff g₁ g₂ gamma V 0 hgammaD
  have htarget := covAlong_diff h₁ h₂ (fun s ↦ f (gamma s))
    (fun s ↦ mfderiv I J f (gamma s) (V s)) 0 htargetD
  have htransport :=
    (congrArg (fun z : E ↦ (mfderiv I J f (gamma 0) z : F)) hsource.symm).trans
      (hraw.trans htarget)
  have hnext := congrArg (fun z : F ↦
    CovariantDerivative.difference (metricCov h₁) (metricCov h₂) (f (gamma 0))
      (mfderiv I J f (gamma 0) (V 0)) z) hchain
  have hfinal := htransport.trans hnext
  convert! hfinal using 1 <;> simp only [V, hY]
  all_goals (congr 2; exact hvelocity.symm)


theorem connectionDifference_norm_le_of_local_isometry_on
    (g₁ g₂ : SmoothRiemannianMetric I M) (h₁ h₂ : SmoothRiemannianMetric J N)
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : IsLocalDiffeomorphOn I J ∞ f U)
    (hmetric₁ : ∀ (x : M), x ∈ U → ∀ v w : TangentSpace I x,
      g₁.inner x v w = h₁.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w))
    (hmetric₂ : ∀ (x : M), x ∈ U → ∀ v w : TangentSpace I x,
      g₂.inner x v w = h₂.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w))
    {x : M} (hx : x ∈ U) {A : ℝ}
    (hbound : ∀ v w : TangentSpace I x,
      Real.sqrt (g₂.inner x
        (CovariantDerivative.difference (metricCov g₁) (metricCov g₂) x v w)
        (CovariantDerivative.difference (metricCov g₁) (metricCov g₂) x v w)) ≤
      A * Real.sqrt (g₂.inner x v v) * Real.sqrt (g₂.inner x w w))
    (u w : TangentSpace J (f x)) :
    Real.sqrt (h₂.inner (f x)
      (CovariantDerivative.difference (metricCov h₁) (metricCov h₂) (f x) u w)
      (CovariantDerivative.difference (metricCov h₁) (metricCov h₂) (f x) u w)) ≤
    A * Real.sqrt (h₂.inner (f x) u u) * Real.sqrt (h₂.inner (f x) w w) := by
  let L := (hf ⟨x, hx⟩).mfderivToContinuousLinearEquiv (by simp)
  obtain ⟨v, hv⟩ := L.surjective u
  obtain ⟨z, hz⟩ := L.surjective w
  change mfderiv I J f x v = u at hv
  change mfderiv I J f x z = w at hz
  subst u w
  have htransport := connectionDifference_map_of_local_isometry_on
    g₁ g₂ h₁ h₂ hU hf hmetric₁ hmetric₂ hx v z
  rw [← htransport, ← hmetric₂ x hx, ← hmetric₂ x hx, ← hmetric₂ x hx]
  exact hbound v z

end DifferentialGeometry.Geometry.Connection
