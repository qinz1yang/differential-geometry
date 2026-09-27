import DifferentialGeometry.Geometry.Exponential.DiagonalExponential.InverseBranch

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

namespace DiagonalInverseBranch

theorem inv_is_min_of_fiber_ball_subset
    {g : SmoothRiemannianMetric I M}
    {hEnorm : IsMetricNorm (I := I) (M := M) g}
    {p y pt : M} (B : DiagonalInverseBranch (I := I) g hEnorm p)
    {r : ℝ} (hd : riemannianEDist I y pt < ENNReal.ofReal r)
    (hsource : ∀ v : TangentSpace I y, Real.sqrt (g.inner y v v) < r →
      (⟨y, v⟩ : TangentBundle I M) ∈ B.hom.source) :
    ∃ v : TangentSpace I y,
      (y, pt) ∈ B.dom ∧
      B.inv (y, pt) = (⟨y, v⟩ : TangentBundle I M) ∧
      expMapIntrinsic (I := I) g hEnorm y v = pt ∧
      Real.sqrt (g.inner y v v) = (riemannianEDist I y pt).toReal := by
  have hfin := ne_of_lt (hd.trans ENNReal.ofReal_lt_top)
  obtain ⟨v, hexp, hlen⟩ :=
    hopf_rinow_expMapIntrinsic_surjective_minimizing_of_ne_top g hEnorm y pt hfin
  have hv : Real.sqrt (g.inner y v v) < r := by
    rw [hlen]
    exact (ENNReal.lt_ofReal_iff_toReal_lt hfin).mp hd
  have hvsrc := hsource v hv
  have hmap : B.hom (⟨y, v⟩ : TangentBundle I M) = (y, pt) := by
    exact (B.hom_eq hvsrc).trans (by simp only [diagExp_apply, hexp])
  exact ⟨v, hmap ▸ B.hom.map_source hvsrc, B.inv_eq_of_exp hvsrc hexp, hexp, hlen⟩

theorem inv_eq_of_fiber_ball_subset
    {g : SmoothRiemannianMetric I M}
    {hEnorm : IsMetricNorm (I := I) (M := M) g}
    {p₁ p₂ y pt : M}
    (B₁ : DiagonalInverseBranch (I := I) g hEnorm p₁)
    (B₂ : DiagonalInverseBranch (I := I) g hEnorm p₂)
    {r : ℝ} (hd : riemannianEDist I y pt < ENNReal.ofReal r)
    (hsource₁ : ∀ v : TangentSpace I y, Real.sqrt (g.inner y v v) < r →
      (⟨y, v⟩ : TangentBundle I M) ∈ B₁.hom.source)
    (hsource₂ : ∀ v : TangentSpace I y, Real.sqrt (g.inner y v v) < r →
      (⟨y, v⟩ : TangentBundle I M) ∈ B₂.hom.source) :
    B₁.inv (y, pt) = B₂.inv (y, pt) := by
  obtain ⟨v, _, hv₁, hexp, hlen⟩ := B₁.inv_is_min_of_fiber_ball_subset hd hsource₁
  have hfin := ne_of_lt (hd.trans ENNReal.ofReal_lt_top)
  have hv₂ := B₂.inv_eq_of_exp (hsource₂ v (by
    rw [hlen]
    exact (ENNReal.lt_ofReal_iff_toReal_lt hfin).mp hd)) hexp
  exact hv₁.trans hv₂.symm

end DiagonalInverseBranch
end Exponential
end Riemannian
end Geometry
end DifferentialGeometry
end
