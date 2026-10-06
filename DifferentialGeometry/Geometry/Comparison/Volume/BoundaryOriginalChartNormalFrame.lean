import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryOriginalChartFrame
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryOriginalChartParallelAlign
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Construction.Existence
import DifferentialGeometry.Topology.VectorField.PartialDiffeomorphLinearization

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set TopologicalSpace
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.VectorField
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
  {ι : Type*} [DecidableEq ι]

private theorem x124_normal_frame_tangent_cast
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Type*} [TopologicalSpace K] {L : ModelWithCorners ℝ F K}
    {N : Type*} [TopologicalSpace N] [ChartedSpace K N]
    {x y : N} (hxy : x = y) (w : TangentSpace L y) :
    (hxy.symm ▸ w : TangentSpace L x) = w := by
  cases hxy
  rfl

private theorem x124_normal_frame_inner_cast
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Type*} [TopologicalSpace K] {L : ModelWithCorners ℝ F K}
    {N : Type*} [TopologicalSpace N] [ChartedSpace K N] [IsManifold L ∞ N]
    (g : SmoothRiemannianMetric L N) {x y : N} (hxy : x = y)
    (v w : TangentSpace L y) :
    g.inner x (hxy.symm ▸ v) (hxy.symm ▸ w) = g.inner y v w := by
  cases hxy
  rfl

private theorem x124_normal_frame_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

/-- A normal parallel orthonormal frame in a pole-chart extension pulls back to a genuine
parallel normal frame for the original metric on its true interior. -/
theorem originalCorner_extension_normal_frame
    (g : SmoothRiemannianMetric I M) (p : M)
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) E) (O : Opens E)
    (hG : ∀ y ∈ (O : Set E) ∩ range I, ∀ v w : E,
      G.inner y v w = DifferentialGeometry.Geometry.Connection.metricFlatModelInChart
        g p y v w)
    (ρ : ℝ → DifferentialGeometry.Manifold.intrinsicInterior I ∞
      x124_normal_frame_infty_ne_zero (M := M))
    (δ : ℝ → E) (J : Set ℝ)
    (hρchart : ∀ s ∈ J, (ρ s : M) ∈
      (DifferentialGeometry.Manifold.interiorChart I ∞ p).source)
    (hcoord : ∀ s ∈ J, extChartAt I p (ρ s : M) = δ s)
    (hρO : ∀ s ∈ J, δ s ∈ O)
    (hδ : ∀ s ∈ J, MDifferentiableAt 𝓘(ℝ, ℝ) (𝓘(ℝ, E)) δ s)
    (W : ι → ∀ s, TangentSpace 𝓘(ℝ, E) (δ s))
    (hW : ∀ i s, s ∈ J → ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, E)).tangent 2
      (fun r => (⟨δ r, W i r⟩ : TangentBundle (𝓘(ℝ, E)) E)) s)
    (hpar : ∀ i s, s ∈ J → covDerivAlong G δ (W i) s = 0)
    (hON : ∀ s, s ∈ J → ∀ i j,
      G.inner (δ s) (W i s) (W j s) = if i = j then 1 else 0)
    (hperp : ∀ s, s ∈ J → ∀ i,
      G.inner (δ s) (W i s) (mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, E)) δ s 1) = 0)
    (hunit : ∀ s, s ∈ J →
      G.inner (δ s) (mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, E)) δ s 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, E)) δ s 1) = 1)
    (x₀ : DifferentialGeometry.Manifold.intrinsicInterior I ∞
      x124_normal_frame_infty_ne_zero (M := M))
    (hx₀chart : (x₀ : M) ∈
      (DifferentialGeometry.Manifold.interiorChart I ∞ p).source)
    (hx₀coord : extChartAt I p (x₀ : M) = δ 0)
    (hx₀O : δ 0 ∈ O) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      x124_normal_frame_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    let k := boundaryInteriorAtlasMetric g
    let F := fun z : U => extChartAt I p (z : M)
    let S := {z : U | (z : M) ∈
        (DifferentialGeometry.Manifold.interiorChart I ∞ p).source ∧ F z ∈ O}
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) U E ∞,
      Φ.source = S ∧ (∀ z ∈ S, Φ z = F z) ∧
      (∀ z ∈ S, ∀ v w : TangentSpace 𝓘(ℝ, E) z,
        k.inner z v w = G.inner (Φ z)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ z v)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ z w)) ∧
      (∀ s, s ∈ J → Φ.symm (δ s) = ρ s) ∧
      (∀ i s, s ∈ J →
        covDerivAlong k (fun r => Φ.symm (δ r))
          (fun r => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ.symm : E → U)
            (δ r) (W i r)) s = 0) ∧
      (∀ s, s ∈ J → ∀ i j,
        k.inner (Φ.symm (δ s))
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ.symm : E → U) (δ s) (W i s))
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ.symm : E → U) (δ s) (W j s)) =
            if i = j then 1 else 0) ∧
      (∀ s, s ∈ J → ∀ i,
        k.inner (Φ.symm (δ s))
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ.symm : E → U) (δ s) (W i s))
          (curveVelocity (I := 𝓘(ℝ, E)) (fun r => Φ.symm (δ r)) s) = 0) ∧
      (∀ s, s ∈ J →
        k.inner (Φ.symm (δ s))
          (curveVelocity (I := 𝓘(ℝ, E)) (fun r => Φ.symm (δ r)) s)
          (curveVelocity (I := 𝓘(ℝ, E)) (fun r => Φ.symm (δ r)) s) = 1) := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    x124_normal_frame_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  let k := boundaryInteriorAtlasMetric g
  let F := fun z : U => extChartAt I p (z : M)
  let S := {z : U | (z : M) ∈
      (DifferentialGeometry.Manifold.interiorChart I ∞ p).source ∧ F z ∈ O}
  dsimp only
  have hx₀S : x₀ ∈ S := by
    refine ⟨hx₀chart, ?_⟩
    change extChartAt I p (x₀ : M) ∈ O
    rw [hx₀coord]
    exact hx₀O
  obtain ⟨Φ, hsource, hmap, hmetric⟩ :=
    boundaryOriginal_chart_partial_isometry g p G O hG ⟨x₀, hx₀S⟩
  have hx₀Φ : x₀ ∈ Φ.source := hsource.symm ▸ hx₀S
  have hmap₀ : Φ x₀ = δ 0 := (hmap x₀ hx₀S).trans hx₀coord
  have hinv₀ : Φ.symm (δ 0) = x₀ :=
    (congrArg Φ.symm hmap₀.symm).trans (Φ.left_inv' hx₀Φ)
  have hmetric' : ∀ z ∈ Φ.source, ∀ v w : TangentSpace 𝓘(ℝ, E) z,
      G.inner (Φ z) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ z v)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ z w) = k.inner z v w := by
    intro z hz v w
    rw [hsource] at hz
    exact (hmetric z hz v w).symm
  have hpoint (s : ℝ) (hs : s ∈ J) : Φ (ρ s) = δ s := by
    have hsS : ρ s ∈ S := by
      refine ⟨hρchart s hs, ?_⟩
      change extChartAt I p (ρ s : M) ∈ O
      rw [hcoord s hs]
      exact hρO s hs
    exact (hmap (ρ s) hsS).trans (hcoord s hs)
  have hsourcePoint (s : ℝ) (hs : s ∈ J) : ρ s ∈ Φ.source :=
    hsource.symm ▸ (show ρ s ∈ S from by
      refine ⟨hρchart s hs, ?_⟩
      change extChartAt I p (ρ s : M) ∈ O
      rw [hcoord s hs]
      exact hρO s hs)
  have htarget (s : ℝ) (hs : s ∈ J) : δ s ∈ Φ.target := by
    exact (hpoint s hs) ▸ Φ.map_source (hsourcePoint s hs)
  have hinv (s : ℝ) (hs : s ∈ J) : Φ.symm (δ s) = ρ s :=
    (congrArg Φ.symm (hpoint s hs).symm).trans (Φ.left_inv' (hsourcePoint s hs))
  have hpointInv (s : ℝ) (hs : s ∈ J) : Φ (Φ.symm (δ s)) = δ s :=
    Φ.right_inv' (htarget s hs)
  have hsourceInv (s : ℝ) (hs : s ∈ J) : Φ.symm (δ s) ∈ S := by
    have hsS : ρ s ∈ S := by
      refine ⟨hρchart s hs, ?_⟩
      change extChartAt I p (ρ s : M) ∈ O
      rw [hcoord s hs]
      exact hρO s hs
    rw [hinv s hs]
    exact hsS
  have hfieldParallel (i : ι) (s : ℝ) (hs : s ∈ J) :
      covDerivAlong k (fun r => Φ.symm (δ r))
        (fun r => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ.symm : E → U)
          (δ r) (W i r)) s = 0 :=
    partialIsometry_pullback_parallel_on_target k G Φ hmetric' δ (W i)
      (htarget s hs) (hδ s hs) (hW i s hs) (hpar i s hs)
  have hforward (i : ι) (s : ℝ) (hs : s ∈ J) :
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ (Φ.symm (δ s))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ.symm : E → U) (δ s) (W i s)) = W i s := by
    have hsource' : Φ.symm (δ s) ∈ Φ.source := Φ.map_target' (htarget s hs)
    have hinvD := inverse_mfderiv_partialDiffeomorph Φ
      (by simp : (∞ : WithTop ℕ∞) ≠ 0) hsource'
    rw [hpointInv s hs] at hinvD
    change (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ (Φ.symm (δ s)))
        ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ.symm : E → U) (δ s)) (W i s)) = W i s
    rw [← hinvD]
    exact (isInvertible_mfderiv_partialDiffeomorph Φ
      (by simp : (∞ : WithTop ℕ∞) ≠ 0) hsource').self_apply_inverse (W i s)
  have hforwardCast (i : ι) (s : ℝ) (hs : s ∈ J) :
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ (Φ.symm (δ s))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ.symm : E → U) (δ s) (W i s)) =
          (hpointInv s hs).symm ▸ W i s := by
    have hcast := x124_normal_frame_tangent_cast (L := 𝓘(ℝ, E))
      (hpointInv s hs) (W i s)
    exact (hforward i s hs).trans hcast.symm
  have hcurve (s : ℝ) (hs : s ∈ J) :
      (fun r => Φ (Φ.symm (δ r))) =ᶠ[𝓝 s] δ := by
    have hcontinuous := (hδ s hs).continuousAt
    filter_upwards [hcontinuous.preimage_mem_nhds
      (Φ.open_target.mem_nhds (htarget s hs))] with r hr
    exact Φ.right_inv' hr
  have hvel (s : ℝ) (hs : s ∈ J) :
      mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, E)) δ s 1 =
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ (Φ.symm (δ s))
          (mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, E)) (fun r => Φ.symm (δ r)) s 1) := by
    have hsymm : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ.symm : E → U) (δ s) :=
      (Φ.contMDiffOn_invFun.contMDiffAt
        (Φ.open_target.mem_nhds (htarget s hs))).mdifferentiableAt (by simp)
    have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
        (fun r => Φ.symm (δ r)) s := hsymm.comp s (hδ s hs)
    have hΦ : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) Φ (Φ.symm (δ s)) :=
      (Φ.contMDiffOn_toFun.contMDiffAt
        (Φ.open_source.mem_nhds (Φ.map_target' (htarget s hs)))).mdifferentiableAt (by simp)
    have hcomp := mfderiv_comp_apply s hΦ hγ (1 : ℝ)
    have heq := (hcurve s hs).mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, E))
    have heq1 := congrArg (fun A : ℝ →L[ℝ] E => A 1) heq
    exact heq1.symm.trans hcomp
  have hvelCast (s : ℝ) (hs : s ∈ J) :
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ (Φ.symm (δ s))
        (curveVelocity (I := 𝓘(ℝ, E)) (fun r => Φ.symm (δ r)) s) =
          (hpointInv s hs).symm ▸ mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, E)) δ s 1 := by
    have hcast := x124_normal_frame_tangent_cast (L := 𝓘(ℝ, E))
      (hpointInv s hs) (mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, E)) δ s 1)
    exact (hvel s hs).symm.trans hcast.symm
  have hinnerCast (s : ℝ) (hs : s ∈ J)
      (v w : TangentSpace (𝓘(ℝ, E)) (δ s)) :
      G.inner (Φ (Φ.symm (δ s)))
          ((hpointInv s hs).symm ▸ v) ((hpointInv s hs).symm ▸ w) =
        G.inner (δ s) v w := by
    exact x124_normal_frame_inner_cast G (hpointInv s hs) v w
  have hframeON (s : ℝ) (hs : s ∈ J) (i j : ι) :
      k.inner (Φ.symm (δ s))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ.symm : E → U) (δ s) (W i s))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ.symm : E → U) (δ s) (W j s)) =
          if i = j then 1 else 0 := by
    have hm := hmetric (Φ.symm (δ s)) (hsourceInv s hs)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ.symm : E → U) (δ s) (W i s))
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ.symm : E → U) (δ s) (W j s))
    calc
      _ = G.inner (Φ (Φ.symm (δ s)))
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ (Φ.symm (δ s))
            (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ.symm : E → U) (δ s) (W i s)))
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ (Φ.symm (δ s))
            (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ.symm : E → U) (δ s) (W j s))) := hm
      _ = G.inner (Φ (Φ.symm (δ s)))
          ((hpointInv s hs).symm ▸ W i s) ((hpointInv s hs).symm ▸ W j s) := by
        rw [hforwardCast i s hs, hforwardCast j s hs]
      _ = G.inner (δ s) (W i s) (W j s) := hinnerCast s hs _ _
      _ = _ := hON s hs i j
  have hframePerp (s : ℝ) (hs : s ∈ J) (i : ι) :
      k.inner (Φ.symm (δ s))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ.symm : E → U) (δ s) (W i s))
        (curveVelocity (I := 𝓘(ℝ, E)) (fun r => Φ.symm (δ r)) s) = 0 := by
    have hmetVelocity := hmetric (Φ.symm (δ s)) (hsourceInv s hs)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ.symm : E → U) (δ s) (W i s))
      (curveVelocity (I := 𝓘(ℝ, E)) (fun r => Φ.symm (δ r)) s)
    calc
      _ = G.inner (Φ (Φ.symm (δ s)))
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ (Φ.symm (δ s))
            (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Φ.symm : E → U) (δ s) (W i s)))
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ (Φ.symm (δ s))
            (curveVelocity (I := 𝓘(ℝ, E)) (fun r => Φ.symm (δ r)) s)) := hmetVelocity
      _ = G.inner (Φ (Φ.symm (δ s)))
          ((hpointInv s hs).symm ▸ W i s)
          ((hpointInv s hs).symm ▸ mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, E)) δ s 1) := by
        rw [hforwardCast i s hs, hvelCast s hs]
      _ = G.inner (δ s) (W i s)
          (mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, E)) δ s 1) := hinnerCast s hs _ _
      _ = 0 := hperp s hs i
  have hframeUnit (s : ℝ) (hs : s ∈ J) :
      k.inner (Φ.symm (δ s))
        (curveVelocity (I := 𝓘(ℝ, E)) (fun r => Φ.symm (δ r)) s)
        (curveVelocity (I := 𝓘(ℝ, E)) (fun r => Φ.symm (δ r)) s) = 1 := by
    have hmetVelocity := hmetric (Φ.symm (δ s)) (hsourceInv s hs)
      (curveVelocity (I := 𝓘(ℝ, E)) (fun r => Φ.symm (δ r)) s)
      (curveVelocity (I := 𝓘(ℝ, E)) (fun r => Φ.symm (δ r)) s)
    calc
      _ = G.inner (Φ (Φ.symm (δ s)))
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ (Φ.symm (δ s))
            (curveVelocity (I := 𝓘(ℝ, E)) (fun r => Φ.symm (δ r)) s))
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ (Φ.symm (δ s))
            (curveVelocity (I := 𝓘(ℝ, E)) (fun r => Φ.symm (δ r)) s)) := hmetVelocity
      _ = G.inner (Φ (Φ.symm (δ s)))
          ((hpointInv s hs).symm ▸ mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, E)) δ s 1)
          ((hpointInv s hs).symm ▸ mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, E)) δ s 1) := by
        rw [hvelCast s hs]
      _ = G.inner (δ s)
          (mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, E)) δ s 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, E)) δ s 1) := hinnerCast s hs _ _
      _ = 1 := hunit s hs
  exact ⟨Φ, hsource, hmap, hmetric, hinv, hfieldParallel, hframeON,
    hframePerp, hframeUnit⟩

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

end
