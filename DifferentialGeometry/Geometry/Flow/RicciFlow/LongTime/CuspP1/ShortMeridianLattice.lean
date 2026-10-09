import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ShortGeodesicTorusExp

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set Function
open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.Exponential
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection GC.Endpoint
namespace GC.LongTime.CuspP1

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- **Flat torus, exponential lattice** (on the instance-clean copy `TorusT`). -/
theorem exists_exp_lattice_torusT_rays_CPA3 (g : SmoothRiemannianMetric torusModel TorusT)
    (hflat : ∀ (x : TorusT) (v w : TangentSpace torusModel x),
      metricRm04StandardAt g x v w w v = 0) (p : TorusT) :
    ∃ (F : TorusPlane → TorusT) (v₁ v₂ : TorusPlane),
      Continuous F ∧ Surjective F ∧ LinearIndependent ℝ ![v₁, v₂] ∧
      (∀ y z : TorusPlane, F y = F z ↔ ∃ m n : ℤ, z - y = m • v₁ + n • v₂) ∧
      F 0 = p ∧
      ∀ v : TorusPlane, ContMDiff 𝓘(ℝ, ℝ) torusModel ∞ (fun s : ℝ => F (s • v)) ∧
        Geodesic.IsGeodesic (I := torusModel) g (fun s : ℝ => F (s • v)) := by
  have hdim : Module.finrank ℝ TorusPlane = 2 := finrank_torusPlane_CPA2
  let : NeZero (Module.finrank ℝ TorusPlane) := ⟨by rw [hdim]; norm_num⟩
  have hfull : ∀ x (v w z u : TangentSpace torusModel x),
      metricRm04StandardAt g x v w z u = 0 := by
    intro x v w z u
    obtain ⟨a, b, hab⟩ := exists_linearIndependent_pair_of_finrank_eq_two (I := torusModel)
      (M := TorusT) hdim x
    have hden := sectionalCurvatureDenominator_pos_of_linearIndependent g x a b hab
    have h1 := metricRm04StandardAt_sectional_eq_of_finrank_eq_two g hdim x a b
    rw [hflat x a b] at h1
    have hs : metricScalarAt (I := torusModel) g x = 0 := by
      have : metricScalarAt (I := torusModel) g x / 2 = 0 := by
        rcases mul_eq_zero.mp h1.symm with h | h
        · exact h
        · exact absurd h hden.ne'
      linarith
    exact metricRm04StandardAt_eq_zero_of_scalar_eq_zero_of_finrank_eq_two g hdim hs v w z u
  have hR : ∀ x (X Y W : TangentSpace torusModel x),
      riemannOp (LeviCivita (I := torusModel) g) x X Y W = 0 := by
    intro x X Y W
    by_contra hne
    have hpos := g.pos x _ hne
    rw [← rm04_eq_inner_riem g x X Y W, hfull] at hpos
    exact lt_irrefl 0 hpos
  let : IsManifold torusModel 1 TorusT :=
    IsManifold.of_le (I := torusModel) (M := TorusT) (n := (∞ : WithTop ℕ∞)) (by decide)
  let : RiemannianBundle (fun x : TorusT => TangentSpace torusModel x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle TorusPlane (fun x : TorusT => TangentSpace torusModel x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace TorusT := EMetricSpace.ofRiemannianMetric torusModel TorusT
  let : CompleteSpace TorusT := (RiemannianMetricComplete.of_compact g).complete
  have hEg : IsMetricNorm (I := torusModel) (M := TorusT) g := fun z v =>
    tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := torusModel) g z v
  obtain ⟨v₁, v₂, hloc, hsurj, hli, hfib⟩ :=
    exists_exp_lattice_of_flat_CPA2 (I := torusModel) (M := TorusT) hdim torusOrientation_CPA2 g
      hEg hR p
  have hray : ∀ (v : TorusPlane) (s : ℝ),
      expMapIntrinsic (I := torusModel) g hEg p (show TangentSpace torusModel p from s • v) =
        intrinsicGeodesic (I := torusModel) g hEg p (show TangentSpace torusModel p from v) s :=
    fun v s => intrinsicGeodesic_smul (I := torusModel) g hEg p
      (show TangentSpace torusModel p from v) s
  have hfun : ∀ v : TorusPlane, (fun s : ℝ => expMapIntrinsic (I := torusModel) g hEg p
      (show TangentSpace torusModel p from s • v)) =
      intrinsicGeodesic (I := torusModel) g hEg p (show TangentSpace torusModel p from v) :=
    fun v => funext (hray v)
  refine ⟨fun z => expMapIntrinsic (I := torusModel) g hEg p (show TangentSpace torusModel p from z),
    v₁, v₂, hloc.contMDiff.continuous, hsurj, hli, hfib, ?_, fun v => ⟨?_, ?_⟩⟩
  · have h := hray v₁ 0
    rw [zero_smul] at h
    rw [intrinsicGeodesic_zero] at h
    exact h
  · show ContMDiff 𝓘(ℝ, ℝ) torusModel ∞ (fun s : ℝ => expMapIntrinsic (I := torusModel) g hEg p
      (show TangentSpace torusModel p from s • v))
    rw [hfun v]
    exact intrinsicGeodesic_contMDiff (I := torusModel) g hEg p _
  · show Geodesic.IsGeodesic (I := torusModel) g (fun s : ℝ => expMapIntrinsic
      (I := torusModel) g hEg p (show TangentSpace torusModel p from s • v))
    rw [hfun v]
    exact intrinsicGeodesic_isGeodesic (I := torusModel) g hEg p _

/-- Same as `exists_exp_lattice_torusT_rays_CPA3` on `Circle × Circle`. -/
theorem exists_exp_lattice_torus_rays_CPA3 (g : SmoothRiemannianMetric torusModel Torus)
    (hflat : ∀ (x : Torus) (v w : TangentSpace torusModel x),
      metricRm04StandardAt g x v w w v = 0) (p : Torus) :
    ∃ (F : TorusPlane → Torus) (v₁ v₂ : TorusPlane),
      Continuous F ∧ Surjective F ∧ LinearIndependent ℝ ![v₁, v₂] ∧
      (∀ y z : TorusPlane, F y = F z ↔ ∃ m n : ℤ, z - y = m • v₁ + n • v₂) ∧
      F 0 = p ∧
      ∀ v : TorusPlane, ContMDiff 𝓘(ℝ, ℝ) torusModel ∞ (fun s : ℝ => F (s • v)) ∧
        Geodesic.IsGeodesic (I := torusModel) g (fun s : ℝ => F (s • v)) :=
  exists_exp_lattice_torusT_rays_CPA3 (g : SmoothRiemannianMetric torusModel TorusT) hflat (p : TorusT)

end GC.LongTime.CuspP1
