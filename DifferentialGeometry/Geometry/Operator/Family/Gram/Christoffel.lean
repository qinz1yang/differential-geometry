import DifferentialGeometry.Geometry.Operator.Family.Gram.Smoothness
import DifferentialGeometry.Geometry.Connection.ParallelTransport.AlongCurve

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Curvature

open Analysis.Parabolic.TensorSpectral
open Geometry.Operator
open Riemannian.AlongCurve
open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (∞ : WithTop ℕ∞) M]

private lemma chartGramOp_eq_sum {D : RealTimeInterval}
    (G : MetricConnectionFamilyOn (I := I) (M := M) D) (p : M)
    (z : Real × E) (u v : E) :
    inner Real (chartGramOp (I := I) G p z u) v =
      ∑ i : Fin (Module.finrank Real E), ∑ j : Fin (Module.finrank Real E),
        chartGramOnE (I := I) (G.metric z.1) p i j z.2 *
          chartCoord (E := E) i u * chartCoord (E := E) j v := by
  rw [chartGramOp, IsCoercive.gramCLM_apply,
    InnerProductSpace.continuousLinearMapOfBilin_apply]
  simpa only [chartGramOnE_def, chartCoord_def, Module.Basis.equivFun_apply] using
    (chartGramBilin_apply (I := I) (M := M) (G.metric z.1) p
      ((extChartAt I p).symm z.2) u v)

theorem chartGram_spatial {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (p : M) {t : Real} {y : E} (ht : t ∈ D.regular)
    (hy : y ∈ interior (extChartAt I p).target) (q w : E) :
    (1 / 2 : Real) *
        inner Real (((fderiv Real (chartGramOp (I := I) G p) (t, y)) (0, w)) q) q =
      inner Real (chartGramOp (I := I) G p (t, y) q)
        (chartChristoffelContraction (I := I) (G.metric t) p q w y) := by
  classical
  let line : Real → E := fun s => y + s • w
  have hline : HasDerivAt line w 0 := by
    change HasDerivAt (fun s : Real => y + s • w) w 0
    convert (hasDerivAt_const (x := (0 : Real)) y).add
      ((hasDerivAt_id (x := (0 : Real))).smul_const w) using 1
    · ext s
      rfl
    · simp
  have hpair : HasDerivAt (fun s : Real => (t, line s)) (0, w) 0 :=
    (hasDerivAt_const (x := (0 : Real)) t).prodMk hline
  have hGram : DifferentiableAt Real (chartGramOp (I := I) G p) (t, y) := by
    have hs := chartGramOp_smooth (I := I) hG p
      (K := interior (extChartAt I p).target) Subset.rfl
    exact (hs.contDiffAt
      ((D.regular_isOpen.prod isOpen_interior).mem_nhds ⟨ht, hy⟩)).differentiableAt
        (by simp)
  have hOp : HasFDerivAt
      (fun z : Real × E => chartGramOp (I := I) G p z q)
      ((fderiv Real (chartGramOp (I := I) G p) (t, y)).flip q) (t, y) := by
    simpa using hGram.hasFDerivAt.clm_apply
      (hasFDerivAt_const (x := (t, y)) q)
  have hscalar : HasFDerivAt
      (fun z : Real × E => inner Real (chartGramOp (I := I) G p z q) q)
      ((fderivInnerCLM Real
          (chartGramOp (I := I) G p (t, y) q, q)).comp
        (((fderiv Real (chartGramOp (I := I) G p) (t, y)).flip q).prod 0))
      (t, y) :=
    hOp.inner Real (hasFDerivAt_const (x := (t, y)) q)
  have hpair' : HasDerivAt (fun s : Real => (t, y + s • w)) (0, w) 0 := by
    simpa only [line] using hpair
  have hscalar_line := HasFDerivAt.comp_hasDerivAt_of_eq
    (x := (0 : Real)) (hl := hscalar) (hf := hpair') (hy := by simp)
  have hscalar_line' : HasDerivAt
      (fun s : Real => inner Real (chartGramOp (I := I) G p (t, line s) q) q)
      (inner Real
        (((fderiv Real (chartGramOp (I := I) G p) (t, y)) (0, w)) q) q) 0 := by
    simpa [line, Function.comp_def] using hscalar_line
  let gamma : Real → M := fun s => (extChartAt I p).symm (line s)
  have hline_zero : line 0 = y := by simp [line]
  have hline_mem : ∀ᶠ s in 𝓝 (0 : Real),
      line s ∈ interior (extChartAt I p).target :=
    hline.continuousAt.preimage_mem_nhds
      (isOpen_interior.mem_nhds (hline_zero.symm ▸ hy))
  have hcurve_eq : chartCurve (I := I) p gamma =ᶠ[𝓝 (0 : Real)] line := by
    filter_upwards [hline_mem] with s hs
    exact (extChartAt I p).right_inv (interior_subset hs)
  have hcurve : HasDerivAt (chartCurve (I := I) p gamma) w 0 :=
    hline.congr_of_eventuallyEq hcurve_eq
  have hcurve_zero : chartCurve (I := I) p gamma 0 = y := by
    simpa [line] using hcurve_eq.eq_of_nhds
  have hcov := chartGramAlongCurve_hasDerivAt_covariant
    (I := I) (g := G.metric t) p gamma (fun _ => q) (fun _ => q)
    (uPrime := fun _ => w) (Vprime := fun _ => 0) (Wprime := fun _ => 0)
    hcurve (hcurve_zero.symm ▸ hy)
    (hasDerivAt_const (x := (0 : Real)) q)
    (hasDerivAt_const (x := (0 : Real)) q)
  let christ := chartChristoffelContraction (I := I) (G.metric t) p w q y
  have hchrist :
      chartChristoffelContraction (I := I) (G.metric t) p w q y = christ := rfl
  have hsum_left :
      (∑ l : Fin (Module.finrank Real E), ∑ j : Fin (Module.finrank Real E),
        chartGramOnE (I := I) (G.metric t) p l j y *
          chartCoord (E := E) l christ * chartCoord (E := E) j q) =
        inner Real (chartGramOp (I := I) G p (t, y) christ) q := by
    exact (chartGramOp_eq_sum (I := I) G p (t, y) christ q).symm
  have hsum_right :
      (∑ i : Fin (Module.finrank Real E), ∑ l : Fin (Module.finrank Real E),
        chartGramOnE (I := I) (G.metric t) p i l y *
          chartCoord (E := E) i q * chartCoord (E := E) l christ) =
        inner Real (chartGramOp (I := I) G p (t, y) q) christ := by
    exact (chartGramOp_eq_sum (I := I) G p (t, y) q christ).symm
  have hsymm :
      inner Real (chartGramOp (I := I) G p (t, y) christ) q =
        inner Real (chartGramOp (I := I) G p (t, y) q) christ := by
    calc
      _ = inner Real christ (chartGramOp (I := I) G p (t, y) q) :=
        IsSelfAdjoint.isSymmetric (chartGramOp_self (I := I) G p (t, y)) christ q
      _ = _ := real_inner_comm _ _
  have hcov' : HasDerivAt
      (fun s => chartGramAlongCurve (I := I) (G.metric t) p gamma
        (fun _ => q) (fun _ => q) s)
      (2 * inner Real (chartGramOp (I := I) G p (t, y) q) christ) 0 := by
    convert hcov using 1
    simp only [hcurve_zero, zero_add]
    rw [hchrist, hsum_left, hsum_right, hsymm]
    ring
  have hfun :
      (fun s : Real => inner Real (chartGramOp (I := I) G p (t, line s) q) q) =ᶠ[𝓝 0]
        (fun s => chartGramAlongCurve (I := I) (G.metric t) p gamma
          (fun _ => q) (fun _ => q) s) := by
    filter_upwards [hcurve_eq] with s hs
    rw [chartGramAlongCurve_def, hs]
    exact chartGramOp_eq_sum (I := I) G p (t, line s) q q
  have hcov_line := hcov'.congr_of_eventuallyEq hfun
  have hderiv := hscalar_line'.unique hcov_line
  dsimp only [christ] at hderiv
  rw [chartChristoffelContraction_symm (I := I) (G.metric t) p q w y]
  linarith

end DifferentialGeometry.Geometry.Curvature
