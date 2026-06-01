import DifferentialGeometry.Integral.Connection.Curvature
import DifferentialGeometry.Integral.Connection.RicciIdentitySmoothFrame
import DifferentialGeometry.Integral.Connection.RiemannianFiberNormSq
import DifferentialGeometry.Integral.Connection.ChristoffelCorrectionBasepoint
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# A controlled linear smooth extension of a single tangent vector

For a smooth Riemannian metric `g` on the tangent bundle of `M`, a base point `x : M`, and a
fibre vector `w : TangentSpace I x`, this file builds a tangent-bundle section
`linearExtensionTangent x w : Π b : M, TangentSpace I b` with:

* `linearExtensionTangent x w x = w` (it extends `w`);
* `b ↦ linearExtensionTangent x w b` is `C^∞` as a tangent-bundle section;
* `w ↦ linearExtensionTangent x w` is `ℝ`-linear (`map_zero`, `map_smul`).

Unlike the choice-based `smoothExtensionTangent`, this extension is *controlled*: it is
the **chart-coordinate-constant** vector field built from `w`'s coordinate under the
tangent trivialization centred at `x`, cut off by a smooth bump supported in the chart
source.  Near `x` (where the bump equals `1`) the chart-trivialised representation is
literally the constant `w`-coordinate, so its chart-derivative vanishes; this is the
structural fact behind the covariant `1`-jet bound.

## Main definitions

* `coordExtensionTangent x w b` — the fibre value at `b` of the coordinate-constant field;
* `linearExtensionTangent x w` — the bump-cut-off coordinate-constant section.

## Main theorems

* `linearExtensionTangent_eq` — `linearExtensionTangent x w x = w`.
* `linearExtensionTangent_smooth` — `C^∞`-smoothness of the section.
* `linearExtensionTangent_map_zero`, `linearExtensionTangent_map_smul` — `ℝ`-linearity in `w`.
-/

noncomputable section

open Bundle Manifold Set FiberBundle NormedSpace
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The `triv`-coordinate of `w : T_x M` in the model space, where
`triv := trivializationAt E (TangentSpace I) x`. -/
def tangentCoord (x : M) (w : TangentSpace I x) : E :=
  (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x w

/-- `w ↦ tangentCoord x w` is `ℝ`-linear (it is the application of a continuous linear map). -/
@[simp] lemma tangentCoord_apply (x : M) (w : TangentSpace I x) :
    tangentCoord (I := I) x w =
      (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x w := rfl

lemma tangentCoord_zero (x : M) : tangentCoord (I := I) x 0 = 0 := by
  simp [tangentCoord]

lemma tangentCoord_smul (x : M) (c : ℝ) (w : TangentSpace I x) :
    tangentCoord (I := I) x (c • w) = c • tangentCoord (I := I) x w := by
  simp [tangentCoord]

/-- The fibre value at `b` of the coordinate-constant field attached to `(x, w)`:
re-inject the constant model coordinate `tangentCoord x w` into the fibre `T_b M`
through the tangent trivialization centred at `x`. -/
def coordExtensionTangent (x : M) (w : TangentSpace I x) (b : M) : TangentSpace I b :=
  (trivializationAt E (TangentSpace I) x).symmL ℝ b (tangentCoord (I := I) x w)

@[simp] lemma coordExtensionTangent_apply (x : M) (w : TangentSpace I x) (b : M) :
    coordExtensionTangent (I := I) x w b =
      (trivializationAt E (TangentSpace I) x).symmL ℝ b (tangentCoord (I := I) x w) := rfl

/-- At the base point `x` the coordinate-constant field recovers `w` itself. -/
lemma coordExtensionTangent_self (x : M) (w : TangentSpace I x) :
    coordExtensionTangent (I := I) x w x = w := by
  classical
  have hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  simp only [coordExtensionTangent_apply, tangentCoord_apply]
  exact (trivializationAt E (TangentSpace I) x).symmL_continuousLinearMapAt hx w

/-- `w ↦ coordExtensionTangent x w b` sends `0` to `0`. -/
lemma coordExtensionTangent_map_zero (x : M) (b : M) :
    coordExtensionTangent (I := I) x (0 : TangentSpace I x) b = 0 := by
  rw [coordExtensionTangent_apply, tangentCoord_zero, map_zero]

/-- `w ↦ coordExtensionTangent x w b` commutes with scalar multiplication. -/
lemma coordExtensionTangent_map_smul (x : M) (c : ℝ) (w : TangentSpace I x) (b : M) :
    coordExtensionTangent (I := I) x (c • w) b =
      c • coordExtensionTangent (I := I) x w b := by
  simp only [coordExtensionTangent_apply, tangentCoord_smul, map_smul]

/-- The coordinate-constant field, as a total-space section, is `C^∞` on the base set of the
trivialization at `x`. -/
lemma coordExtensionTangent_contMDiffOn (x : M) (w : TangentSpace I x) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (T% (coordExtensionTangent (I := I) x w))
      (trivializationAt E (TangentSpace I) x).baseSet := by
  classical
  have hiff :=
    ((trivializationAt E (TangentSpace I) x)).contMDiffOn_section_baseSet_iff
      (IB := I) (n := ∞)
      (s := fun b => coordExtensionTangent (I := I) x w b)
  refine hiff.mpr ?_
  have hconst : ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun _ : M => tangentCoord (I := I) x w)
      (trivializationAt E (TangentSpace I) x).baseSet :=
    contMDiffOn_const
  refine hconst.congr ?_
  intro b hb
  change (trivializationAt E (TangentSpace I) x
      ⟨b, coordExtensionTangent (I := I) x w b⟩).2 = tangentCoord (I := I) x w
  have happ :
      (trivializationAt E (TangentSpace I) x
        ⟨b, (trivializationAt E (TangentSpace I) x).symm b
          (tangentCoord (I := I) x w)⟩).2
        = tangentCoord (I := I) x w := by
    have h := (trivializationAt E (TangentSpace I) x).apply_mk_symm hb
      (tangentCoord (I := I) x w)
    simpa using congrArg Prod.snd h
  simpa [coordExtensionTangent, Trivialization.symmL_apply] using happ

/-- A choice of smooth bump function centred at `x`, used to cut off the coordinate-constant
field to a globally smooth section.  Its support lies in the chart source, and it equals `1`
on a neighbourhood of `x`. -/
def linExtBump (x : M) : SmoothBumpFunction I x :=
  Classical.arbitrary (SmoothBumpFunction I x)

/-- **The controlled linear tangent extension.** The coordinate-constant field attached to
`(x, w)` multiplied by a smooth bump centred at `x` whose support lies in the chart source.
It extends `w`, is `C^∞`, and is `ℝ`-linear in `w`. -/
def linearExtensionTangent (x : M) (w : TangentSpace I x) :
    Π b : M, TangentSpace I b :=
  fun b => (linExtBump (I := I) x : M → ℝ) b • coordExtensionTangent (I := I) x w b

@[simp] lemma linearExtensionTangent_apply (x : M) (w : TangentSpace I x) (b : M) :
    linearExtensionTangent (I := I) x w b =
      (linExtBump (I := I) x : M → ℝ) b • coordExtensionTangent (I := I) x w b := rfl

/-- The bump equals `1` at its centre `x`. -/
lemma linExtBump_eq_one (x : M) : (linExtBump (I := I) x : M → ℝ) x = 1 :=
  (linExtBump (I := I) x).eq_one

/-- **Extension property:** `linearExtensionTangent x w x = w`. -/
theorem linearExtensionTangent_eq (x : M) (w : TangentSpace I x) :
    linearExtensionTangent (I := I) x w x = w := by
  rw [linearExtensionTangent_apply, linExtBump_eq_one, one_smul,
    coordExtensionTangent_self]

/-- **Homogeneity:** `linearExtensionTangent x 0 = 0`. -/
theorem linearExtensionTangent_map_zero (x : M) :
    linearExtensionTangent (I := I) x (0 : TangentSpace I x) = 0 := by
  funext b
  rw [linearExtensionTangent_apply, coordExtensionTangent_map_zero, smul_zero]
  rfl

/-- **Scalar homogeneity:** `linearExtensionTangent x (c • w) = c • linearExtensionTangent x w`. -/
theorem linearExtensionTangent_map_smul (x : M) (c : ℝ) (w : TangentSpace I x) :
    linearExtensionTangent (I := I) x (c • w) =
      c • linearExtensionTangent (I := I) x w := by
  funext b
  rw [Pi.smul_apply, linearExtensionTangent_apply, linearExtensionTangent_apply,
    coordExtensionTangent_map_smul, smul_comm]

/-- **Smoothness:** `b ↦ linearExtensionTangent x w b` is a `C^∞` tangent-bundle section. -/
theorem linearExtensionTangent_smooth [T2Space M] (x : M) (w : TangentSpace I x) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (linearExtensionTangent (I := I) x w)) := by
  classical
  set u : Set M := (chartAt H x).source with hu_def
  set ψ : M → ℝ := (linExtBump (I := I) x : M → ℝ) with hψ_def
  have hψ_smooth : ContMDiffOn I 𝓘(ℝ) ∞ ψ u :=
    (linExtBump (I := I) x).contMDiff.contMDiffOn
  have hu_open : IsOpen u := (chartAt H x).open_source
  have hψ_tsupport : tsupport ψ ⊆ u :=
    (linExtBump (I := I) x).tsupport_subset_chartAt_source
  have hs_smooth : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => coordExtensionTangent (I := I) x w b)) u := by
    rw [show u = (trivializationAt E (TangentSpace I) x).baseSet from rfl]
    exact coordExtensionTangent_contMDiffOn (I := I) x w
  have h := ContMDiffOn.smul_section_of_tsupport (𝕜 := ℝ) (n := ∞)
    (V := TangentSpace I) hψ_smooth hu_open hψ_tsupport hs_smooth
  have h_eq : (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b
        (linearExtensionTangent (I := I) x w b)) =
      (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b
        ((ψ • fun b' : M => coordExtensionTangent (I := I) x w b') b)) := by
    funext b
    change TotalSpace.mk' E b (linearExtensionTangent (I := I) x w b) =
      TotalSpace.mk' E b ((ψ b) • coordExtensionTangent (I := I) x w b)
    rw [linearExtensionTangent_apply]
  rw [h_eq]
  exact h

section Reduction

variable [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- On the base set of the trivialization at `x`, the chart-trivialised representation of the
coordinate-constant field is the constant model coordinate `tangentCoord x w`. -/
lemma chartE_section_repr_coordExtensionTangent_eq
    (x : M) (w : TangentSpace I x) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) x).baseSet) :
    chartE_section_repr (I := I) x (coordExtensionTangent (I := I) x w) b =
      tangentCoord (I := I) x w := by
  rw [chartE_section_repr_eq_trivToE, coordExtensionTangent_apply]
  exact (trivializationAt E (TangentSpace I) x).continuousLinearMapAt_symmL (R := ℝ) hb _

/-- Near `x`, the chart-trivialised representation of `linearExtensionTangent x w` (in the
self-chart at `x`) equals the constant `tangentCoord x w`: the bump is `1` near `x` and the
underlying field has constant representation on the base set. -/
lemma chartE_section_repr_linearExtensionTangent_eventuallyEq_const
    (x : M) (w : TangentSpace I x) :
    chartE_section_repr (I := I) x (linearExtensionTangent (I := I) x w)
      =ᶠ[𝓝 x] (fun _ : M => tangentCoord (I := I) x w) := by
  classical
  have h1 : {b : M | (linExtBump (I := I) x : M → ℝ) b = 1} ∈ 𝓝 x :=
    (linExtBump (I := I) x).eventuallyEq_one
  have h2 : (trivializationAt E (TangentSpace I) x).baseSet ∈ 𝓝 x := by
    rw [show (trivializationAt E (TangentSpace I) x).baseSet = (chartAt H x).source from rfl]
    exact (chartAt H x).open_source.mem_nhds (mem_chart_source H x)
  filter_upwards [h1, h2] with b hb1 hb2
  have hWb : linearExtensionTangent (I := I) x w b =
      coordExtensionTangent (I := I) x w b := by
    rw [linearExtensionTangent_apply, hb1, one_smul]
  show chartE_section_repr (I := I) x (linearExtensionTangent (I := I) x w) b =
    tangentCoord (I := I) x w
  rw [chartE_section_repr_eq_trivToE, hWb, ← chartE_section_repr_eq_trivToE]
  exact chartE_section_repr_coordExtensionTangent_eq (I := I) x w hb2

/-- The Fréchet derivative of the chart-pulled representation of `linearExtensionTangent x w`
vanishes at the basepoint: the representation is locally constant near `x` (in the self-chart),
so its pullback under `(extChartAt I x).symm` is locally constant near `extChartAt I x x`. -/
lemma fderiv_chartE_section_repr_linearExtensionTangent_eq_zero
    (x : M) (w : TangentSpace I x) :
    fderiv ℝ (chartE_section_repr (I := I) x (linearExtensionTangent (I := I) x w)
        ∘ (extChartAt I x).symm) (extChartAt I x x) = 0 := by
  classical
  have hconst :
      (chartE_section_repr (I := I) x (linearExtensionTangent (I := I) x w)
          ∘ (extChartAt I x).symm)
        =ᶠ[𝓝 (extChartAt I x x)] (fun _ : E => tangentCoord (I := I) x w) := by
    have hsymm_cont : ContinuousAt (extChartAt I x).symm (extChartAt I x x) :=
      continuousAt_extChartAt_symm x
    have hsymm_pt : (extChartAt I x).symm (extChartAt I x x) = x :=
      extChartAt_to_inv x
    have hmem : {b : M | chartE_section_repr (I := I) x
          (linearExtensionTangent (I := I) x w) b = tangentCoord (I := I) x w}
        ∈ 𝓝 ((extChartAt I x).symm (extChartAt I x x)) := by
      rw [hsymm_pt]
      exact chartE_section_repr_linearExtensionTangent_eventuallyEq_const (I := I) x w
    have hpre :
        (extChartAt I x).symm ⁻¹'
          {b : M | chartE_section_repr (I := I) x (linearExtensionTangent (I := I) x w) b
            = tangentCoord (I := I) x w}
          ∈ 𝓝 (extChartAt I x x) :=
      hsymm_cont.preimage_mem_nhds hmem
    filter_upwards [hpre] with y hy
    exact hy
  rw [hconst.fderiv_eq]
  exact fderiv_const_apply (𝕜 := ℝ) (tangentCoord (I := I) x w)

/-- **Pure-Christoffel reduction of the covariant `1`-jet at the basepoint.** For any tangent
vector `v : T_x M`, the covariant derivative of `linearExtensionTangent x w` along `v`,
evaluated at `x`, collapses to the metric Christoffel contraction of `v` with `w`:
the bump and the chart-derivative contribute nothing at the centre. -/
theorem covApply_linearExtensionTangent_basepoint_eq
    (g : SmoothRiemannianMetric I M) (x : M) (w : TangentSpace I x)
    (v : TangentSpace I x) :
    (LeviCivita (I := I) g).toFun (linearExtensionTangent (I := I) x w) x v =
      trivFromE (I := I) x x
        (christoffelCorrection (I := I) g x x (tangentCoord (I := I) x w) v) := by
  classical
  have hself : x ∈ chartLeviCivitaGoodSet (I := I) x :=
    self_mem_chartLeviCivitaGoodSet (I := I) (α := x)
  have hMDiff : MDiffAt (T% (linearExtensionTangent (I := I) x w)) x :=
    (linearExtensionTangent_smooth (I := I) x w).mdifferentiableAt (by norm_num)
  rw [LeviCivita_chart_apply (I := I) g x hself hMDiff v]
  rw [chartLeviCivita_apply (I := I) g x (linearExtensionTangent (I := I) x w) hself v]
  rw [fderiv_chartE_section_repr_linearExtensionTangent_eq_zero (I := I) x w]
  have hreprx : chartE_section_repr (I := I) x (linearExtensionTangent (I := I) x w) x =
      tangentCoord (I := I) x w := by
    rw [chartE_section_repr_eq_trivToE, linearExtensionTangent_eq]
    rfl
  rw [hreprx]
  simp

end Reduction

end Connection
end Integral
end DifferentialGeometry
