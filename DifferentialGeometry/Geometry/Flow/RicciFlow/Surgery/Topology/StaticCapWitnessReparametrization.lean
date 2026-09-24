import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCapQuotientReparametrization
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingDiffeomorph
import DifferentialGeometry.Topology.Handle.Manifold
import DifferentialGeometry.Topology.Manifold.ClosedBallLinearIsometry

section

set_option autoImplicit false
noncomputable section

open Set Function Manifold
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Topology.Handle
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.StaticCapWitness

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M]
  {g : SmoothRiemannianMetric ThreeModel M} {δ : ℝ} {k : ℕ}
  {neck : NormalizedNeck g δ k} {fixed : StaticCapScaffold} {D : ℝ} {m : ℕ} {ε : ℝ}
  (S : StaticCapWitness neck fixed D m ε)
  (B : letI := S.ballCharts; ThreeBall ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ThreeBall)
  (a : Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2)
  (hboundary : ∀ y, B (sphereToThreeBall y) = sphereToThreeBall (a y))

def reparametrizeCap : StaticCapWitness neck fixed D m ε := by
  letI := S.ballCharts
  letI := S.ballSmooth
  letI := S.retainedCharts
  letI := S.retainedSmooth
  letI := S.modelCoreCharts
  letI := S.modelCoreSmooth
  letI := S.quotientCharts
  letI := S.quotientSmooth
  let e := staticCapQuotientReparametrization δ S.attaching.toHomeomorph a.toHomeomorph
    B.toHomeomorph hboundary
  let newCharts : ChartedSpace ThreeSpace (StaticCapQuotient δ (a.trans S.attaching).toHomeomorph) :=
    chartedSpaceOfHomeomorph e
  letI := newCharts
  let eD : StaticCapQuotient δ (a.trans S.attaching).toHomeomorph ≃ₘ⟮ThreeModel, ThreeModel⟯
      StaticCapQuotient δ S.attaching.toHomeomorph :=
    { toEquiv := e.toEquiv
      contMDiff_toFun := contMDiff_homeomorph_of_chartedSpaceOfHomeomorph e ThreeModel ∞
      contMDiff_invFun := contMDiff_homeomorph_symm_of_chartedSpaceOfHomeomorph e ThreeModel ∞ }
  have hRange : range (S.cap ∘ B) = range S.cap := B.surjective.range_comp S.cap
  refine { S with
    attaching := a.trans S.attaching
    quotientCharts := newCharts
    quotientSmooth := isManifoldOfHomeomorph ThreeModel e
    quotientPresentation := eD.trans S.quotientPresentation
    cap := S.cap.comp ⟨B, B.continuous⟩
    cap_smooth := isSmoothEmbedding_diffeomorph_precomp S.cap S.cap_smooth B
    retained_quotient := ?_
    cap_quotient := ?_
    cover := ?_
    overlap := ?_
    boundary_eq := ?_
    tip_interior := ?_
    capChart_range := ?_ }
  · intro x
    change S.retained x = S.quotientPresentation (e (Quotient.mk _ (Sum.inl x)))
    exact S.retained_quotient x
  · intro x
    change S.cap (B x) = S.quotientPresentation (e (Quotient.mk _ (Sum.inr x)))
    exact S.cap_quotient (B x)
  · change range S.retained ∪ range (S.cap ∘ B) = univ
    rw [hRange]
    exact S.cover
  · change range S.retained ∩ range (S.cap ∘ B) = range (S.cap ∘ B ∘ sphereToThreeBall)
    rw [hRange]
    have heq : S.cap ∘ B ∘ sphereToThreeBall = (S.cap ∘ sphereToThreeBall) ∘ a := by
      funext y
      exact congrArg S.cap (hboundary y)
    rw [heq]
    erw [a.surjective.range_comp (S.cap ∘ sphereToThreeBall)]
    exact S.overlap
  · intro y
    change S.cap (B (sphereToThreeBall y)) =
      S.retained ⟨(S.attaching (a y), 0), le_rfl, inv_pos.mpr neck.delta_pos⟩
    rw [hboundary]
    exact S.boundary_eq (a y)
  · obtain ⟨x, hx, hxt⟩ := S.tip_interior
    refine ⟨B.symm x, ?_, ?_⟩
    · have hle : ‖(B.symm x : ThreeSpace)‖ ≤ 1 := mem_closedBall_zero_iff.mp (B.symm x).property
      by_contra! hn
      have heq : ‖(B.symm x : ThreeSpace)‖ = 1 := le_antisymm hle hn
      let y : Sphere 2 := ⟨B.symm x, mem_sphere_zero_iff_norm.mpr heq⟩
      have hy : sphereToThreeBall y = B.symm x := Subtype.ext rfl
      have hb := hboundary y
      rw [hy, B.apply_symm_apply] at hb
      have hnorm : ‖(x : ThreeSpace)‖ = 1 := by
        rw [hb]
        exact mem_sphere_zero_iff_norm.mp (a y).property
      exact (ne_of_lt hx) hnorm
    · change S.cap (B (B.symm x)) = S.tip
      rw [B.apply_symm_apply]
      exact hxt
  · change range S.capChart = range (S.cap ∘ B)
    rw [hRange]
    exact S.capChart_range

@[simp] theorem reparametrizeCap_cap (x : ThreeBall) :
    (S.reparametrizeCap B a hboundary).cap x = S.cap (B x) := rfl

@[simp] theorem reparametrizeCap_retained :
    (S.reparametrizeCap B a hboundary).retained = S.retained := rfl

@[simp] theorem reparametrizeCap_attaching (y : Sphere 2) :
    (S.reparametrizeCap B a hboundary).attaching y = S.attaching (a y) := rfl

@[simp] theorem reparametrizeCap_metric :
    (S.reparametrizeCap B a hboundary).metric = S.metric := rfl

@[simp] theorem reparametrizeCap_window :
    (S.reparametrizeCap B a hboundary).window = S.window := rfl

@[simp] theorem reparametrizeCap_capChart :
    (S.reparametrizeCap B a hboundary).capChart = S.capChart := rfl

@[simp] theorem reparametrizeCap_collapse :
    (S.reparametrizeCap B a hboundary).collapse = S.collapse := rfl

theorem range_cap_reparametrizeCap :
    range (S.reparametrizeCap B a hboundary).cap = range S.cap :=
  B.surjective.range_comp S.cap

theorem reparametrizeCap_cap_metric (x : ThreeBall) :
    letI := S.ballCharts
    ∀ v w : TangentSpace (𝓡∂ 3) x,
      (S.reparametrizeCap B a hboundary).metric.inner ((S.reparametrizeCap B a hboundary).cap x)
        (mfderiv (𝓡∂ 3) ThreeModel (S.reparametrizeCap B a hboundary).cap x v)
        (mfderiv (𝓡∂ 3) ThreeModel (S.reparametrizeCap B a hboundary).cap x w) =
      S.metric.inner (S.cap (B x))
        (mfderiv (𝓡∂ 3) ThreeModel S.cap (B x) (mfderiv (𝓡∂ 3) (𝓡∂ 3) B x v))
        (mfderiv (𝓡∂ 3) ThreeModel S.cap (B x) (mfderiv (𝓡∂ 3) (𝓡∂ 3) B x w)) := by
  let := S.ballCharts
  intro v w
  change S.metric.inner (S.cap (B x))
    (mfderiv (𝓡∂ 3) ThreeModel (S.cap ∘ B) x v)
    (mfderiv (𝓡∂ 3) ThreeModel (S.cap ∘ B) x w) = _
  rw [mfderiv_comp x (S.cap_smooth.contMDiff.mdifferentiableAt (by simp))
    (B.contMDiff.mdifferentiableAt (by simp))]
  rfl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.StaticCapWitness

end

end

section

set_option autoImplicit false
noncomputable section

open Set Function Manifold
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.StaticCapWitness

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M]
  {g : SmoothRiemannianMetric ThreeModel M} {δ : ℝ} {k : ℕ}
  {neck : NormalizedNeck g δ k} {fixed : StaticCapScaffold} {D : ℝ} {m : ℕ} {ε : ℝ}
  (S : StaticCapWitness neck fixed D m ε)
  (A : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
  (a : Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2)
  (ha : ∀ y : Sphere 2, (a y : ThreeSpace) = A y)

def capLinearIsometryDiffeomorph :
    letI := S.ballCharts
    ThreeBall ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ThreeBall :=
  letI := S.ballCharts
  closedBallLinearIsometryDiffeomorph (𝓡∂ 3) 1 S.ball_induced.isImmersion A

@[simp] theorem capLinearIsometryDiffeomorph_apply (x : ThreeBall) :
    (S.capLinearIsometryDiffeomorph A x : ThreeSpace) = A x := rfl

include ha in
theorem capLinearIsometryDiffeomorph_boundary (y : Sphere 2) :
    S.capLinearIsometryDiffeomorph A (sphereToThreeBall y) = sphereToThreeBall (a y) :=
  Subtype.ext (ha y).symm

def reparametrizeCapOfLinearIsometry : StaticCapWitness neck fixed D m ε :=
  S.reparametrizeCap (S.capLinearIsometryDiffeomorph A) a
    (S.capLinearIsometryDiffeomorph_boundary A a ha)

@[simp] theorem reparametrizeCapOfLinearIsometry_cap (x : ThreeBall) :
    (S.reparametrizeCapOfLinearIsometry A a ha).cap x =
      S.cap (S.capLinearIsometryDiffeomorph A x) := rfl

@[simp] theorem reparametrizeCapOfLinearIsometry_metric :
    (S.reparametrizeCapOfLinearIsometry A a ha).metric = S.metric := rfl

@[simp] theorem reparametrizeCapOfLinearIsometry_retained :
    (S.reparametrizeCapOfLinearIsometry A a ha).retained = S.retained := rfl

@[simp] theorem reparametrizeCapOfLinearIsometry_attaching (y : Sphere 2) :
    (S.reparametrizeCapOfLinearIsometry A a ha).attaching y = S.attaching (a y) := rfl

theorem reparametrizeCapOfLinearIsometry_cap_eq_of_coe_eq
    (B : ThreeBall → ThreeBall) (hB : ∀ x : ThreeBall, (B x : ThreeSpace) = A x) (x : ThreeBall) :
    (S.reparametrizeCapOfLinearIsometry A a ha).cap x = S.cap (B x) := by
  change S.cap (S.capLinearIsometryDiffeomorph A x) = S.cap (B x)
  exact congrArg S.cap (Subtype.ext (hB x).symm)

theorem range_cap_reparametrizeCapOfLinearIsometry :
    range (S.reparametrizeCapOfLinearIsometry A a ha).cap = range S.cap :=
  S.range_cap_reparametrizeCap (S.capLinearIsometryDiffeomorph A) a
    (S.capLinearIsometryDiffeomorph_boundary A a ha)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.StaticCapWitness

end

end
