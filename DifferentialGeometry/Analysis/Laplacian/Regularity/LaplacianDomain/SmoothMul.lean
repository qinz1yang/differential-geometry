import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.LeibnizCompensatedFh
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.LaplacianDomain
import DifferentialGeometry.Analysis.Laplacian.Regularity.LaplacianDomain.VariationalLimitGeneral
import DifferentialGeometry.Analysis.Laplacian.Regularity.SmoothScalar.PreH1
import DifferentialGeometry.Analysis.Laplacian.Regularity.LaplacianDomain.PerChartWitness

/-!
# Smooth-multiplication structure on the variational Laplacian's domain

This file develops the structural ingredients for showing that
`smoothMulLp ρα (H1ComplToLp u_h)` is the `Lp` representative of an element
of `laplacianDomain g`, for `u_h ∈ laplacianDomain g` and `ρα` a smooth
bump function on `M`.

## Contents

* `fHLeibnizResidualCLM` — the hypothesis-free CLM
  `H1Compl g →L[ℝ] Lp ℝ 2 μ_g` corresponding to the smooth-case pointwise
  expression `-2 g(∇ρα, ∇v) - Δρα · v` (the two Leibniz cross terms).

* `phiMulU_h` — the explicit `H1Compl g` element representing `ρα · u_h`,
  defined as `resolvent g (fHLeibniz g α u_h hu_h)` for `u_h ∈ laplacianDomain g`.
  Lies in `laplacianDomain g` by construction.

* `phiMulU_h_smoothToH1Compl` — on smooth `v`, `phiMulU_h α (smoothToH1Compl v) _`
  equals `smoothToH1Compl (pouScalar α v) = smoothToH1Compl (ρα · v)`,
  identifying `phiMulU_h` with the natural smooth multiplication on smooth
  scalars. This is the smooth-case anchor for the density argument extending
  the multiplication to all of `H1Compl g`.

## Future discharge

The Lp identity
```
H1ComplToLp (phiMulU_h α u_h hu_h) = smoothMulLp ρα (H1ComplToLp u_h)
```
(which would discharge `fChartResidual_memW1p_two` unconditionally) is proved
on smooth scalars by `phiMulU_h_smoothToH1Compl` combined with the
identification `H1ComplToLp (smoothToH1Compl (pouScalar α v)) = smoothToLp (pouScalar α v)`
and `smoothMulLp ρα (smoothToLp v) = smoothToLp (pouScalar α v)`. Extending
to all `u_h ∈ laplacianDomain g` requires graph-norm density of smooth scalars
in `laplacianDomain g`, which in turn requires a classical-Laplacian resolvent
mapping `C^∞ → C^∞` on closed manifolds (standard elliptic regularity, not
yet formalised in this codebase).
-/

noncomputable section

open Bundle Manifold MeasureTheory Filter Topology
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace LaplacianDomainSmoothMul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainVariationalLimit
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainVariationalLimitGeneral

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-- The CLM realisation of the residual part of `fHLeibniz`, depending only
on `u_h` (no `laplacianDomain` membership hypothesis). This is the `Lp` class
combination `-2 • gradInnerCLM ρα u_h - smoothMulLp Δρα (H1ComplToLp u_h)`,
representing the smooth-case pointwise expression
`-2 g(∇ρα, ∇v) - Δρα · v` for smooth `v`. -/
noncomputable def fHLeibnizResidualCLM
    (g : SmoothRiemannianMetric I M) (α : M) :
    H1Compl (I := I) (M := M) g →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  -((2 : ℝ) • gradInnerCLM (I := I) (M := M) g
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)) -
    (smoothMulLp (I := I) (M := M) g
      (laplacianOfChartPOU (I := I) (M := M) g α)).comp
      (H1ComplToLp (I := I) (M := M) g)

/-- Application of `fHLeibnizResidualCLM` matches the residual definition
used in `DiffChartBilinearH1ComplFromDomainPow.lean`. -/
@[simp] lemma fHLeibnizResidualCLM_apply
    (g : SmoothRiemannianMetric I M) (α : M) (u_h : H1Compl g) :
    fHLeibnizResidualCLM (I := I) (M := M) g α u_h =
      -((2 : ℝ) • gradInnerCLM (I := I) (M := M) g
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h) -
        smoothMulLp (I := I) (M := M) g
          (laplacianOfChartPOU (I := I) (M := M) g α)
          (H1ComplToLp (I := I) (M := M) g u_h) := by
  unfold fHLeibnizResidualCLM
  rfl

/-- For smooth `v`, `fHLeibnizResidualCLM (smoothToH1Compl v)` is the smooth
arithmetic combination `-2 • gradInnerSmooth ρα v - smoothMulLp Δρα (smoothToLp v)`. -/
theorem fHLeibnizResidualCLM_smoothToH1Compl
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    fHLeibnizResidualCLM (I := I) (M := M) g α
        (smoothToH1Compl (I := I) (M := M) g v) =
      -((2 : ℝ) • gradInnerSmooth (I := I) (M := M) g
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) v) -
        smoothMulLp (I := I) (M := M) g
          (laplacianOfChartPOU (I := I) (M := M) g α)
          (smoothToLp (I := I) (M := M) g v) := by
  rw [fHLeibnizResidualCLM_apply]
  rw [H1ComplToLp_smoothToH1Compl]
  rw [gradInnerCLM_smoothToH1Compl]

/-- The H¹Compl-side analogue of `ρα · u_h`, constructed via the resolvent of
the Leibniz-compensated right-hand side `fHLeibniz`. -/
noncomputable def phiMulU_h
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    H1Compl (I := I) (M := M) g :=
  resolvent (I := I) (M := M) g
    (fHLeibniz (I := I) (M := M) g α u_h hu_h)

/-- `phiMulU_h` lies in `laplacianDomain g` (by construction, as the image of an
`Lp` element under the resolvent). -/
theorem phiMulU_h_mem_laplacianDomain
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    phiMulU_h (I := I) (M := M) g α hu_h ∈
      laplacianDomain (I := I) (M := M) g := by
  unfold phiMulU_h
  rw [laplacianDomain_mem_iff]
  exact ⟨fHLeibniz (I := I) (M := M) g α u_h hu_h, rfl⟩

/-- `phiMulU_h`'s `laplacianDomain.preimage` is `fHLeibniz g α u_h hu_h`. -/
theorem laplacianDomain_preimage_phiMulU_h
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    laplacianDomain.preimage (I := I) (M := M) g
        ⟨phiMulU_h (I := I) (M := M) g α hu_h,
          phiMulU_h_mem_laplacianDomain (I := I) (M := M) g α hu_h⟩ =
      fHLeibniz (I := I) (M := M) g α u_h hu_h := by
  unfold phiMulU_h
  apply resolvent_injective (I := I) (M := M) g
  rw [resolvent_laplacianDomain_preimage_eq]

/-- The smooth-case computation: for smooth `v`,
`phiMulU_h α (smoothToH1Compl v) _ = smoothToH1Compl (pouScalar α v)`,
i.e., the resolvent of `fHLeibniz(smoothToH1Compl v)` equals the smooth lift
of the pointwise product `ρα · v`. -/
theorem phiMulU_h_smoothToH1Compl
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    phiMulU_h (I := I) (M := M) g α
        (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) =
      smoothToH1Compl (I := I) (M := M) g
        (pouScalar (I := I) (M := M) α v) := by
  unfold phiMulU_h
  have h_lp_eq :
      fHLeibniz (I := I) (M := M) g α
          (smoothToH1Compl (I := I) (M := M) g v)
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) =
      smoothToLp (I := I) (M := M) g
        (pouScalar (I := I) (M := M) α v).oneSubLapClassical := by
    apply MeasureTheory.Lp.ext
    have h_aeEq := pouScalar_oneSubLap_aeEq_fHLeibniz_smooth (I := I) (M := M) g α v
    have h_smoothToLp_coeFn :
        ((smoothToLp (I := I) (M := M) g
            (pouScalar (I := I) (M := M) α v).oneSubLapClassical :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
          riemannianVolumeMeasure (I := I) (M := M) g]
        (pouScalar (I := I) (M := M) α v).oneSubLapClassical.toFun :=
      MemLp.coeFn_toLp
        (pouScalar (I := I) (M := M) α v).oneSubLapClassical.memLp_two
    exact h_aeEq.symm.trans h_smoothToLp_coeFn.symm
  rw [h_lp_eq]
  exact (smoothToH1Compl_eq_resolvent_oneSubLap
    (I := I) (M := M) (pouScalar (I := I) (M := M) α v)).symm

end LaplacianDomainSmoothMul
end Laplacian
end Analysis
end DifferentialGeometry

end
