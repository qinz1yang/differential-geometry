import DifferentialGeometry.Geometry.Operator.Laplacian.Barrier
import DifferentialGeometry.Geometry.Operator.Gradient.Regularity
import DifferentialGeometry.Geometry.Operator.Laplacian.Minimum
import DifferentialGeometry.Geometry.Connection.LeviCivita.Koszul.Formula

open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (∞ : WithTop ℕ∞) M] [T2Space M] [SigmaCompactSpace M]

def IsLaplacianLEViscosityAt
    (g : SmoothRiemannianMetric I M) (u : M → Real) (c : Real) (x : M) : Prop :=
  ∀ ψ : M → Real,
    ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞) ψ x →
    ψ x = u x →
    (∀ᶠ y in 𝓝 x, ψ y ≤ u y) →
    laplacian (I := I) (LeviCivita (I := I) g) g ψ x ≤ c

def IsLaplacianLEViscosityOn
    (g : SmoothRiemannianMetric I M) (u b : M → Real) (s : Set M) : Prop :=
  ∀ x ∈ s, IsLaplacianLEViscosityAt (I := I) g u (b x) x

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
theorem IsLaplacianLEBarrierAt.to_viscosity
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    {g : SmoothRiemannianMetric I M} {u : M → Real} {c : Real} {x : M}
    (h : IsLaplacianLEBarrierAt (I := I) g u c x)
    (hx : I.IsInteriorPoint x) :
    IsLaplacianLEViscosityAt (I := I) g u c x := by
  intro ψ hψ hψx hψu
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨φ, hφ, hφx, hup, hlapφ⟩ := h ε hε
  have hmin : IsLocalMin (fun y : M => φ y - ψ y) x := by
    change ∀ᶠ y in 𝓝 x, φ x - ψ x ≤ φ y - ψ y
    filter_upwards [hup, hψu] with y huy hly
    rw [hφx, hψx, sub_self]
    exact sub_nonneg.mpr (hly.trans huy)
  have hsub :
      ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun y : M => φ y - ψ y) x :=
    hφ.sub hψ
  have hsub_diff :
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => φ y - ψ y) x :=
    hsub.mdifferentiableAt (by simp)
  have hsub_one :
      ContMDiffAt I 𝓘(Real, Real) 1
        (fun y : M => φ y - ψ y) x :=
    hsub.of_le (WithTop.coe_le_coe.mpr (le_top : (1 : ℕ∞) ≤ ⊤))
  have hsub_one_near :
      ∀ᶠ y in 𝓝 x,
        ContMDiffAt I 𝓘(Real, Real) 1
          (fun z : M => φ z - ψ z) y :=
    (contMDiffAt_iff_contMDiffAt_nhds (I := I) (I' := 𝓘(Real, Real))
      (n := 1) (by decide)).mp hsub_one
  have hsub_diff_near :
      ∀ᶠ y in 𝓝 x,
        MDifferentiableAt I 𝓘(Real, Real) (fun z : M => φ z - ψ z) y :=
    hsub_one_near.mono fun y hy => hy.mdifferentiableAt (by decide)
  have hgrad :
      MDiffAt
        (T% fun y : M =>
          gradientFun (I := I) g (fun z : M => φ z - ψ z) y) x :=
    (gradientFun_contMDiffAt (I := I) g hsub).mdifferentiableAt (by simp)
  have hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible
      (I := I) (LeviCivita (I := I) g) g := by
    simpa only [LeviCivita] using
      (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g)
  have hlap_sub :
      0 ≤ laplacian (I := I) (LeviCivita (I := I) g) g
        (fun y : M => φ y - ψ y) x :=
    laplacian_nonneg_at_spatial_min_of_metricCompatible_of_isInteriorPoint
      (I := I) (LeviCivita (I := I) g) g hmc hmin hx hsub_diff
        hsub_diff_near hgrad
  rw [laplacian_sub_at (I := I) (LeviCivita (I := I) g) g hφ hψ] at hlap_sub
  exact (sub_nonneg.mp hlap_sub).trans hlapφ

end DifferentialGeometry.Geometry.Operator
