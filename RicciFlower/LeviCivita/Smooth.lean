import RicciFlower.LeviCivita.Torsion
import RicciFlower.VectorBundle.LocalFrameRegularity
import RicciFlower.Tensor.RSTensor.Basis
import RicciFlower.Tensor.RSTensor.NablaOnTensors.Connection.Smooth
import Mathlib.Geometry.Manifold.VectorBundle.Hom

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Smoothness frontier for the Levi-Civita connection

This file is intentionally RicciFlower-only.  Do not import the external
external geometry namespace here.

The previous attempt transferred smoothness from the external synthetic
`KoszulCov` construction.  That was the wrong dependency direction for this
project.  The intended proof of smoothness for `leviCivitaConnectionOfMetric`
should be built from the local-frame/Koszul coefficient route inside
`RicciFlower`, using the existing coordinate-frame Christoffel and tensor
regularity APIs.
-/

noncomputable section

namespace RicciFlower
namespace LeviCivita

open Bundle
open Realized
open Coordinates
open Tensor0SBundle
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

/-- RicciFlower-only record of the already proved geometric Levi-Civita
predicate for the Koszul-defined connection.

The smoothness theorem itself is deliberately not asserted here until it is
proved from the in-tree local-frame/Koszul coefficient API. -/
theorem leviCivitaConnectionOfMetric_isLeviCivita_smoothFile
    (g : SmoothRiemannianMetric I M) :
    IsLeviCivita (I := I) (leviCivitaConnectionOfMetric (I := I) g) g :=
  leviCivitaConnectionOfMetric_isLeviCivita (I := I) g

/-! ## Local-frame metric and Koszul coefficient smoothness

The local-frame route keeps the trivialization `e` fixed on a neighborhood.
Metric coefficients and their frame-directional derivatives are scalar
functions in that fixed local frame; these are the inputs for the Koszul
Christoffel formula.
-/

private def localMetricCoeff
    {ι : Type*}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E) (g : SmoothRiemannianMetric I M)
    (i j : ι) (y : M) : Real :=
  g.inner y (e.localFrame b i y) (e.localFrame b j y)

private theorem localFrame_contMDiffAt
    {ι : Type*}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {x : M} (hx : x ∈ e.baseSet) (i : ι) :
    ContMDiffAt I (I.prod 𝓘(Real, E)) ∞ (T% (e.localFrame b i)) x :=
  (e.isLocalFrameOn_localFrame_baseSet I ∞ b).contMDiffAt
    e.open_baseSet hx i

private theorem localMetricCoeff_contMDiffAt
    {ι : Type*}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet)
    (i j : ι) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M => localMetricCoeff (I := I) e b g i j y) x := by
  have hg :
      ContMDiffAt I
        (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) ∞
        (fun y : M =>
          (⟨y, g.inner y⟩ :
            TotalSpace (E →L[Real] E →L[Real] Real)
              (fun y : M =>
                TangentSpace I y →L[Real] TangentSpace I y →L[Real] Real)))
        x :=
    (g.contMDiff.contMDiffAt (x := x)).of_le (by simp)
  have hi := localFrame_contMDiffAt (I := I) e b hx i
  have hj := localFrame_contMDiffAt (I := I) e b hx j
  have htotal :
      ContMDiffAt I (I.prod 𝓘(Real, Real)) ∞
        (fun y : M =>
          (⟨y, localMetricCoeff (I := I) e b g i j y⟩ :
            TotalSpace Real (Bundle.Trivial M Real))) x := by
    simpa [localMetricCoeff] using
      ContMDiffAt.clm_bundle_apply₂ (F₁ := E) (F₂ := E) hg hi hj
  rw [contMDiffAt_totalSpace] at htotal
  exact htotal.2

private theorem localMetricCoeff_deriv_contMDiffAt
    {ι : Type*}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet)
    (a i j : ι) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        extDerivFun (I := I)
          (fun q : M => localMetricCoeff (I := I) e b g i j q)
          y (e.localFrame b a y)) x := by
  exact extDerivFun_apply_contMDiffAt_of_section
    (I := I)
    (f := fun q : M => localMetricCoeff (I := I) e b g i j q)
    (X := e.localFrame b a)
    (localMetricCoeff_contMDiffAt (I := I) e b g hx i j)
    (localFrame_contMDiffAt (I := I) e b hx a)

private theorem localMetricBracket_contMDiffAt
    {ι : Type*}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet)
    (i j k : ι) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        g.inner y (e.localFrame b i y)
          (VectorField.mlieBracket I (e.localFrame b j) (e.localFrame b k) y)) x := by
  haveI : IsManifold I (minSmoothness Real 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact (inferInstance : IsManifold I 2 M)
  haveI : IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  have hi := localFrame_contMDiffAt (I := I) e b hx i
  have hj := localFrame_contMDiffAt (I := I) e b hx j
  have hk := localFrame_contMDiffAt (I := I) e b hx k
  have hbr :
      ContMDiffAt I (I.prod 𝓘(Real, E)) ∞
        (T% (VectorField.mlieBracket I (e.localFrame b j) (e.localFrame b k))) x := by
    simpa using
      (ContMDiffAt.mlieBracket_vectorField
        (I := I) (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞))
        hj hk (by simp))
  have hg :
      ContMDiffAt I
        (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) ∞
        (fun y : M =>
          (⟨y, g.inner y⟩ :
            TotalSpace (E →L[Real] E →L[Real] Real)
              (fun y : M =>
                TangentSpace I y →L[Real] TangentSpace I y →L[Real] Real)))
        x :=
    (g.contMDiff.contMDiffAt (x := x)).of_le (by simp)
  have htotal :
      ContMDiffAt I (I.prod 𝓘(Real, Real)) ∞
        (fun y : M =>
          (⟨y,
            g.inner y (e.localFrame b i y)
              (VectorField.mlieBracket I (e.localFrame b j) (e.localFrame b k) y)⟩ :
            TotalSpace Real (Bundle.Trivial M Real))) x := by
    exact ContMDiffAt.clm_bundle_apply₂ (F₁ := E) (F₂ := E) hg hi hbr
  rw [contMDiffAt_totalSpace] at htotal
  exact htotal.2

private theorem koszulScalar_localFrame_contMDiffAt
    {ι : Type*}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet)
    (i j k : ι) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        koszulScalar (I := I) g (e.localFrame b i) (e.localFrame b j)
          (e.localFrame b k) y) x := by
  have h1 := localMetricCoeff_deriv_contMDiffAt (I := I) e b g hx i j k
  have h2 := localMetricCoeff_deriv_contMDiffAt (I := I) e b g hx j k i
  have h3 := localMetricCoeff_deriv_contMDiffAt (I := I) e b g hx k i j
  have h4 := localMetricBracket_contMDiffAt (I := I) e b g hx i j k
  have h5 := localMetricBracket_contMDiffAt (I := I) e b g hx j k i
  have h6 := localMetricBracket_contMDiffAt (I := I) e b g hx k i j
  simpa [koszulScalar, directionalDeriv, localMetricCoeff] using
    (((h1.add h2).sub h3).sub h4).add h5 |>.add h6

/-- The coordinate functional associated to a basis vector of the model fiber. -/
private noncomputable def coordCLM {ι : Type*} (b : Module.Basis ι Real E) (i : ι) :
    E →L[Real] Real :=
  LinearMap.toContinuousLinearMap (b.coord i)

/-- The elementary bilinear form `(v,w) ↦ v_i w_j` in a model-fiber basis. -/
private noncomputable def basisBilin {ι : Type*} (b : Module.Basis ι Real E) (i j : ι) :
    E →L[Real] E →L[Real] Real :=
  (coordCLM (E := E) b i).smulRight (coordCLM (E := E) b j)

private theorem basisBilin_apply {ι : Type*} (b : Module.Basis ι Real E) (i j : ι)
    (v w : E) :
    basisBilin (E := E) b i j v w = b.coord i v * b.coord j w := by
  simp [basisBilin, coordCLM]

/-- The metric bilinear form written in a fixed local frame, as a model-fiber
continuous bilinear map. This avoids nested Hom-bundle trivialization while
retaining the exact local-frame Gram matrix. -/
private noncomputable def localMetricFlatBasis {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) (y : M) :
    E →L[Real] E →L[Real] Real :=
  ∑ i : ι, ∑ j : ι,
    localMetricCoeff (I := I) e b g i j y • basisBilin (E := E) b i j

private theorem localMetricFlatBasis_apply {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) (y : M) (v w : E) :
    localMetricFlatBasis (I := I) e b g y v w =
      ∑ i : ι, ∑ j : ι,
        localMetricCoeff (I := I) e b g i j y * b.coord i v * b.coord j w := by
  simp [localMetricFlatBasis, basisBilin_apply, mul_assoc]

private theorem localFrame_sum_coord_smul
    {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {x : M} (hx : x ∈ e.baseSet) (v : E) :
    (∑ i : ι, b.coord i v • e.localFrame b i x) = e.symmL Real x v := by
  calc
    (∑ i : ι, b.coord i v • e.localFrame b i x)
        = ∑ i : ι, b.coord i v • e.symmL Real x (b i) := by
          apply Finset.sum_congr rfl
          intro i _
          simp [e.localFrame_apply_of_mem_baseSet (b := b) hx,
            Bundle.Trivialization.basisAt]
    _ = e.symmL Real x (∑ i : ι, b.coord i v • b i) := by
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro i _
          simp [map_smul]
    _ = e.symmL Real x v := by
          have hsum : (∑ i : ι, b.coord i v • b i) = v := by
            simp [b.sum_repr v]
          rw [hsum]

private theorem localMetricFlatBasis_eq_inner {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet) (v w : E) :
    localMetricFlatBasis (I := I) e b g x v w =
      g.inner x (e.symmL Real x v) (e.symmL Real x w) := by
  have hv := localFrame_sum_coord_smul (I := I) e b hx v
  have hw := localFrame_sum_coord_smul (I := I) e b hx w
  calc
    localMetricFlatBasis (I := I) e b g x v w
        = g.inner x
            (∑ i : ι, b.coord i v • e.localFrame b i x)
            (∑ j : ι, b.coord j w • e.localFrame b j x) := by
          simp [localMetricFlatBasis_apply, localMetricCoeff, map_sum, map_smul,
            smul_eq_mul, Finset.mul_sum, mul_left_comm, mul_comm]
          conv_rhs => rw [Finset.sum_comm]
    _ = g.inner x (e.symmL Real x v) (e.symmL Real x w) := by
          rw [hv, hw]

private theorem localMetricFlatBasis_isInvertible {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet) :
    (localMetricFlatBasis (I := I) e b g x).IsInvertible := by
  haveI : CompleteSpace (E →L[Real] Real) := inferInstance
  let A : E →ₗ[Real] (E →L[Real] Real) :=
    (localMetricFlatBasis (I := I) e b g x).toLinearMap
  have hker : LinearMap.ker A = ⊥ := by
    ext v
    constructor
    · intro hv
      change A v = 0 at hv
      have hself :
          localMetricFlatBasis (I := I) e b g x v v = 0 := by
        exact congrArg (fun L : E →L[Real] Real => L v) hv
      have hinner :
          g.inner x (e.symmL Real x v) (e.symmL Real x v) = 0 := by
        simpa [localMetricFlatBasis_eq_inner (I := I) e b g hx v v] using hself
      by_contra hvne
      have hsymm_ne : e.symmL Real x v ≠ 0 := by
        intro hzero
        have hmap := congrArg (e.continuousLinearMapAt Real x) hzero
        have hcancel :
            e.continuousLinearMapAt Real x (e.symmL Real x v) = v :=
          e.continuousLinearMapAt_symmL (R := Real) hx v
        rw [hcancel] at hmap
        exact hvne (by simpa using hmap)
      exact False.elim ((ne_of_gt (g.pos x (e.symmL Real x v) hsymm_ne)) hinner)
    · intro hv
      have hv0 : v = 0 := by simpa using hv
      simp [A, hv0]
  have hdim :
      Module.finrank Real E = Module.finrank Real (E →L[Real] Real) := by
    calc
      Module.finrank Real E = Module.finrank Real (Module.Dual Real E) :=
        Subspace.dual_finrank_eq.symm
      _ = Module.finrank Real (E →L[Real] Real) :=
        (LinearMap.toContinuousLinearMap :
          (E →ₗ[Real] Real) ≃ₗ[Real] (E →L[Real] Real)).finrank_eq
  let Aequiv : E ≃ₗ[Real] (E →L[Real] Real) :=
    A.linearEquivOfInjective (LinearMap.ker_eq_bot.mp hker) hdim
  let Acle : E ≃L[Real] (E →L[Real] Real) :=
    Aequiv.toContinuousLinearEquiv
  have hA : (Acle : E →L[Real] E →L[Real] Real) =
      localMetricFlatBasis (I := I) e b g x := by
    ext v w
    change Aequiv v w = localMetricFlatBasis (I := I) e b g x v w
    rw [LinearMap.linearEquivOfInjective_apply]
    rfl
  rw [← hA]
  exact ContinuousLinearMap.isInvertible_equiv

private theorem localMetricFlatBasis_contMDiffAt {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet) :
    ContMDiffAt I 𝓘(Real, E →L[Real] E →L[Real] Real) ∞
      (fun y => localMetricFlatBasis (I := I) e b g y) x := by
  unfold localMetricFlatBasis
  refine ContMDiffAt.sum fun i _ => ContMDiffAt.sum fun j _ => ?_
  exact (localMetricCoeff_contMDiffAt (I := I) e b g hx i j).smul contMDiffAt_const

/-- Inverse metric coefficients in a fixed local-frame basis, obtained by
inverting the local-frame Gram operator. -/
private noncomputable def localInvMetricCoeff {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) (k l : ι) (y : M) : Real :=
  b.coord k
    ((ContinuousLinearMap.inverse (localMetricFlatBasis (I := I) e b g y))
      (coordCLM (E := E) b l))

private theorem localInvMetricCoeff_contMDiffAt_of_isInvertible {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet)
    (hInv : (localMetricFlatBasis (I := I) e b g x).IsInvertible) (k l : ι) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M => localInvMetricCoeff (I := I) e b g k l y) x := by
  haveI : CompleteSpace E := FiniteDimensional.complete Real E
  let εl : E →L[Real] Real := coordCLM (E := E) b l
  let εk : E →L[Real] Real := coordCLM (E := E) b k
  have hflat :=
    localMetricFlatBasis_contMDiffAt (I := I) e b g hx
  have hinv :
      ContMDiffAt I 𝓘(Real, (E →L[Real] Real) →L[Real] E) ∞
        (fun y : M =>
          ContinuousLinearMap.inverse (localMetricFlatBasis (I := I) e b g y)) x := by
    simpa [Function.comp_def] using
      (hInv.contDiffAt_map_inverse (n := ∞)).contMDiffAt.comp x hflat
  have happ :
      ContMDiffAt I 𝓘(Real, E) ∞
        (fun y : M =>
          ContinuousLinearMap.inverse (localMetricFlatBasis (I := I) e b g y) εl) x := by
    simpa [εl] using hinv.clm_apply contMDiffAt_const
  simpa [localInvMetricCoeff, εk, εl, coordCLM] using
    (contMDiffAt_const (c := εk)).clm_apply happ

private theorem localInvMetricCoeff_contMDiffAt {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet) (k l : ι) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M => localInvMetricCoeff (I := I) e b g k l y) x :=
  localInvMetricCoeff_contMDiffAt_of_isInvertible (I := I) e b g hx
    (localMetricFlatBasis_isInvertible (I := I) e b g hx) k l

private theorem localMetricFlatBasis_eq_dual_sum {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) (x : M) (v : E) :
    localMetricFlatBasis (I := I) e b g x v =
      ∑ l : ι,
        localMetricFlatBasis (I := I) e b g x v (b l) • coordCLM (E := E) b l := by
  ext w
  calc
    localMetricFlatBasis (I := I) e b g x v w
        = localMetricFlatBasis (I := I) e b g x v
            (∑ l : ι, b.coord l w • b l) := by
          rw [show (∑ l : ι, b.coord l w • b l) = w by
            exact b.sum_repr w]
    _ = ∑ l : ι,
          localMetricFlatBasis (I := I) e b g x v (b l) *
            b.coord l w := by
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro l _
          simp [smul_eq_mul, mul_comm]
    _ = (∑ l : ι,
        localMetricFlatBasis (I := I) e b g x v (b l) • coordCLM (E := E) b l) w := by
          simp [coordCLM, smul_eq_mul]

private theorem basis_coord_eq_sum_localInvMetric_flat {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet)
    (k : ι) (v : E) :
    b.coord k v =
      ∑ l : ι,
        localInvMetricCoeff (I := I) e b g k l x *
          localMetricFlatBasis (I := I) e b g x v (b l) := by
  let A := localMetricFlatBasis (I := I) e b g x
  have hInv := localMetricFlatBasis_isInvertible (I := I) e b g hx
  calc
    b.coord k v = b.coord k (A.inverse (A v)) := by
      rw [hInv.inverse_apply_self]
    _ = b.coord k
        (A.inverse
          (∑ l : ι, A v (b l) • coordCLM (E := E) b l)) := by
          rw [← localMetricFlatBasis_eq_dual_sum (I := I) e b g x v]
    _ = ∑ l : ι, A v (b l) *
          b.coord k (A.inverse (coordCLM (E := E) b l)) := by
          simp [map_sum, map_smul, smul_eq_mul]
    _ = ∑ l : ι,
        localInvMetricCoeff (I := I) e b g k l x *
          localMetricFlatBasis (I := I) e b g x v (b l) := by
          apply Finset.sum_congr rfl
          intro l _
          simp [A, localInvMetricCoeff, mul_comm]

private theorem localFrame_coeff_eq_sum_localInvMetric_inner {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet)
    (k : ι) (V : TangentSpace I x) :
    e.localFrame_coeff I b k x V =
      ∑ l : ι,
        localInvMetricCoeff (I := I) e b g k l x *
          g.inner x (e.localFrame b l x) V := by
  let v : E := e.continuousLinearMapAt Real x V
  have hcoeff :
      e.localFrame_coeff I b k x V = b.coord k v := by
    classical
    let σ : (y : M) → TangentSpace I y := fun y => if h : x = y then h ▸ V else 0
    have hσx : σ x = V := by
      simp [σ]
    have hσ := Bundle.Trivialization.localFrame_coeff_apply_of_mem_baseSet
      (𝕜 := Real) (F := E) (V := (TangentSpace I : M → Type _)) (I := I)
      (e := e) (b := b) hx σ k
    rw [hσx] at hσ
    rw [hσ]
    simp [v, Bundle.Trivialization.basisAt, Bundle.Trivialization.continuousLinearMapAt_apply,
      e.coe_linearMapAt_of_mem hx]
  have hflat :
      ∀ l : ι,
        localMetricFlatBasis (I := I) e b g x v (b l) =
          g.inner x V (e.localFrame b l x) := by
    intro l
    have hv : e.symmL Real x v = V := by
      exact e.symmL_continuousLinearMapAt (R := Real) hx V
    have hl : e.symmL Real x (b l) = e.localFrame b l x := by
      rw [e.localFrame_apply_of_mem_baseSet (b := b) hx]
      simp [Bundle.Trivialization.basisAt]
    rw [localMetricFlatBasis_eq_inner (I := I) e b g hx v (b l), hv, hl]
  rw [hcoeff, basis_coord_eq_sum_localInvMetric_flat (I := I) e b g hx]
  apply Finset.sum_congr rfl
  intro l _
  rw [hflat l, g.symm x V (e.localFrame b l x)]

private theorem lc_christoffel_eq_koszul_sum {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet)
    (i j k : ι) :
    e.localFrame_coeff I b k x
        ((leviCivitaConnectionOfMetric (I := I) g (e.localFrame b j) x)
          (e.localFrame b i x)) =
      (1 / 2 : Real) *
        ∑ l : ι,
          localInvMetricCoeff (I := I) e b g k l x *
            koszulScalar (I := I) g (e.localFrame b i) (e.localFrame b j)
              (e.localFrame b l) x := by
  let A : TangentSpace I x :=
    (leviCivitaConnectionOfMetric (I := I) g (e.localFrame b j) x)
      (e.localFrame b i x)
  have hcoeff := localFrame_coeff_eq_sum_localInvMetric_inner
    (I := I) e b g hx k A
  have hinner :
      ∀ l : ι,
        g.inner x (e.localFrame b l x) A =
          (1 / 2 : Real) *
            koszulScalar (I := I) g (e.localFrame b i) (e.localFrame b j)
              (e.localFrame b l) x := by
    intro l
    have hi := (localFrame_contMDiffAt (I := I) e b hx i).mdifferentiableAt (by simp)
    have hj := (localFrame_contMDiffAt (I := I) e b hx j).mdifferentiableAt (by simp)
    have hl := (localFrame_contMDiffAt (I := I) e b hx l).mdifferentiableAt (by simp)
    have hKos := leviCivitaConnectionOfMetric_inner_eq_koszulScalar
      (I := I) g (e.localFrame b i) (e.localFrame b j)
      (e.localFrame b l) x hi hj hl
    calc
      g.inner x (e.localFrame b l x) A = g.inner x A (e.localFrame b l x) := by
        exact g.symm x (e.localFrame b l x) A
      _ = (1 / 2 : Real) *
          koszulScalar (I := I) g (e.localFrame b i) (e.localFrame b j)
            (e.localFrame b l) x := by
          simpa [A] using hKos
  rw [hcoeff]
  calc
    (∑ l : ι,
        localInvMetricCoeff (I := I) e b g k l x * g.inner x (e.localFrame b l x) A)
        = ∑ l : ι,
            localInvMetricCoeff (I := I) e b g k l x *
              ((1 / 2 : Real) *
                koszulScalar (I := I) g (e.localFrame b i) (e.localFrame b j)
                  (e.localFrame b l) x) := by
          apply Finset.sum_congr rfl
          intro l _
          rw [hinner l]
    _ = (1 / 2 : Real) *
        ∑ l : ι,
          localInvMetricCoeff (I := I) e b g k l x *
            koszulScalar (I := I) g (e.localFrame b i) (e.localFrame b j)
              (e.localFrame b l) x := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l _
          ring

private theorem lc_christoffel_contMDiffAt {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet)
    (i j k : ι) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        e.localFrame_coeff I b k y
          ((leviCivitaConnectionOfMetric (I := I) g (e.localFrame b j) y)
            (e.localFrame b i y))) x := by
  have hRhs :
      ContMDiffAt I 𝓘(Real, Real) ∞
        (fun y : M =>
          (1 / 2 : Real) *
            ∑ l : ι,
              localInvMetricCoeff (I := I) e b g k l y *
                koszulScalar (I := I) g (e.localFrame b i) (e.localFrame b j)
                  (e.localFrame b l) y) x := by
    refine contMDiffAt_const.mul (ContMDiffAt.sum fun l _ => ?_)
    exact (localInvMetricCoeff_contMDiffAt (I := I) e b g hx k l).mul
      (koszulScalar_localFrame_contMDiffAt (I := I) e b g hx i j l)
  have heq :
      (fun y : M =>
        e.localFrame_coeff I b k y
          ((leviCivitaConnectionOfMetric (I := I) g (e.localFrame b j) y)
            (e.localFrame b i y))) =ᶠ[𝓝 x]
      fun y : M =>
        (1 / 2 : Real) *
          ∑ l : ι,
            localInvMetricCoeff (I := I) e b g k l y *
              koszulScalar (I := I) g (e.localFrame b i) (e.localFrame b j)
                (e.localFrame b l) y := by
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    exact lc_christoffel_eq_koszul_sum (I := I) e b g hy i j k
  exact hRhs.congr_of_eventuallyEq heq

/-- In any trivialization-induced local frame, the Levi-Civita connection sends a locally smooth
tangent section to a locally smooth Hom-bundle section. -/
theorem leviCivitaConnectionOfMetric_homSection_contMDiffAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet)
    (hσdiff : ∀ᶠ y in 𝓝 x, MDiffAt (T% σ) y)
    (hσ : ContMDiffAt I (I.prod 𝓘(Real, E)) ∞ (T% σ) x) :
    ContMDiffAt I (I.prod 𝓘(Real, E →L[Real] E)) ∞
      (fun y : M =>
        (⟨y, leviCivitaConnectionOfMetric (I := I) g σ y⟩ :
          TotalSpace (E →L[Real] E)
            (fun y : M => TangentSpace I y →L[Real] TangentSpace I y))) x :=
  covariantDerivative_homSection_contMDiffAt_of_coeff
    (I := I) (leviCivitaConnectionOfMetric (I := I) g) e b hx hσdiff hσ
    (fun i k j => lc_christoffel_contMDiffAt (I := I) e b g hx i j k)

/-- The Levi-Civita connection of a smooth Riemannian metric is locally smooth as a
covariant derivative. -/
theorem leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
    (g : SmoothRiemannianMetric I M) :
    CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (I := I) (E := E) (M := M)
      (leviCivitaConnectionOfMetric (I := I) g) ∞ := by
  intro u hu
  refine ⟨?_⟩
  intro σ hσ x hx
  let e : Trivialization E
      (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M) :=
    trivializationAt E (TangentSpace I : M → Type _) x
  let b := Module.finBasis Real E
  have hxBase : x ∈ e.baseSet := by
    simp [e]
  have hσAtTop :
      ContMDiffAt I (I.prod 𝓘(Real, E)) ((∞ : WithTop ℕ∞) + 1) (T% σ) x :=
    hσ.contMDiffAt (hu.mem_nhds hx)
  have hσAt :
      ContMDiffAt I (I.prod 𝓘(Real, E)) ∞ (T% σ) x :=
    hσAtTop.of_le (by simp)
  have hσdiff : ∀ᶠ y in 𝓝 x, MDiffAt (T% σ) y := by
    filter_upwards [hu.mem_nhds hx] with y hy
    have hyTop :
        ContMDiffAt I (I.prod 𝓘(Real, E)) ((∞ : WithTop ℕ∞) + 1) (T% σ) y :=
      hσ.contMDiffAt (hu.mem_nhds hy)
    have hyOne :
        ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞) (T% σ) y :=
      hyTop.of_le (by simp)
    exact hyOne.mdifferentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  exact
    (leviCivitaConnectionOfMetric_homSection_contMDiffAt
      (I := I) e b g hxBase hσdiff hσAt).contMDiffWithinAt

/-- Fixed-coordinate-frame metric components are smooth throughout the
coordinate-frame domain. -/
theorem metric_coordinateFrame_component_contMDiffAt_of_mem
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun p : M =>
        g.inner p (coordinateFrameAt (I := I) x₀ i p)
          (coordinateFrameAt (I := I) x₀ j p)) x := by
  have hg :
      ContMDiffAt I
        (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) ∞
        (fun p : M =>
          (⟨p, g.inner p⟩ :
            TotalSpace (E →L[Real] E →L[Real] Real)
              (fun p : M =>
                TangentSpace I p →L[Real] TangentSpace I p →L[Real] Real)))
        x :=
    (g.contMDiff.contMDiffAt (x := x)).of_le (by simp)
  have hi :
      ContMDiffAt I (I.prod 𝓘(Real, E)) ∞
        (fun p : M =>
          (⟨p, coordinateFrameAt (I := I) x₀ i p⟩ :
            TotalSpace E (TangentSpace I : M -> Type _))) x :=
    (coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
      (coordinateFrameSet_open (I := I) x₀)
      hx i
  have hj :
      ContMDiffAt I (I.prod 𝓘(Real, E)) ∞
        (fun p : M =>
          (⟨p, coordinateFrameAt (I := I) x₀ j p⟩ :
            TotalSpace E (TangentSpace I : M -> Type _))) x :=
    (coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
      (coordinateFrameSet_open (I := I) x₀)
      hx j
  have htotal :
      ContMDiffAt I (I.prod 𝓘(Real, Real)) ∞
        (fun p : M =>
          (⟨p,
            g.inner p (coordinateFrameAt (I := I) x₀ i p)
              (coordinateFrameAt (I := I) x₀ j p)⟩ :
            TotalSpace Real (Bundle.Trivial M Real))) x :=
    ContMDiffAt.clm_bundle_apply₂ (F₁ := E) (F₂ := E) hg hi hj
  rw [contMDiffAt_totalSpace] at htotal
  exact htotal.2

/-- Coordinate-frame metric components are smooth at the chart center. -/
theorem metric_coordinateFrame_component_contMDiffAt
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun p : M =>
        g.inner p (coordinateFrameAt (I := I) x₀ i p)
          (coordinateFrameAt (I := I) x₀ j p)) x₀ :=
  metric_coordinateFrame_component_contMDiffAt_of_mem
    (I := I) g x₀ (coordinateFrameAt_mem (I := I) x₀) i j

/-- Coordinate directional derivatives of metric components are smooth at the
chart center. -/
theorem metric_coordinateFrame_component_directional_contMDiffAt
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (a i j : CoordinateIdx (𝕜 := Real) E) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun p : M =>
        extDerivFun (I := I)
          (fun q : M =>
            g.inner q (coordinateFrameAt (I := I) x₀ i q)
              (coordinateFrameAt (I := I) x₀ j q))
          p (coordinateFrameAt (I := I) x₀ a p)) x₀ := by
  have hf := metric_coordinateFrame_component_contMDiffAt
    (I := I) g x₀ i j
  have ha :
      ContMDiffAt I (I.prod 𝓘(Real, E)) ∞
        (fun p : M =>
          (⟨p, coordinateFrameAt (I := I) x₀ a p⟩ :
            TotalSpace E (TangentSpace I : M -> Type _))) x₀ :=
    (coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
      (coordinateFrameSet_open (I := I) x₀)
      (coordinateFrameAt_mem (I := I) x₀) a
  exact extDerivFun_apply_contMDiffAt_of_section
    (I := I) (f := fun q : M =>
      g.inner q (coordinateFrameAt (I := I) x₀ i q)
        (coordinateFrameAt (I := I) x₀ j q))
    (X := coordinateFrameAt (I := I) x₀ a) hf ha

/-! ## Fixed-chart metric flat map

The inverse metric components should be proved smooth by applying
`ContinuousLinearMap.inverse` to this fixed-chart flat map.  This keeps the
argument over an arbitrary finite-dimensional complete model space `E`, rather
than choosing `E = Real^n`.
-/

private noncomputable def metricFlatContinuousEquiv
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    E ≃L[Real] (E →L[Real] Real) :=
  ((metricFlatEquiv (I := I) g x₀).trans
    (LinearMap.toContinuousLinearMap :
      (E →ₗ[Real] Real) ≃ₗ[Real] (E →L[Real] Real))).toContinuousLinearEquiv

private theorem metricFlatContinuousEquiv_apply
    (g : SmoothRiemannianMetric I M) (x₀ : M) (v w : E) :
    ((metricFlatContinuousEquiv (I := I) g x₀) v) w = g.inner x₀ v w := by
  change ((metricFlatEquiv (I := I) g x₀) v) w = g.inner x₀ v w
  rw [metricFlatEquiv_apply]

/-- The metric flat map represented in the tangent trivialization centered at
`x₀`, viewed over the model chart target. -/
noncomputable def metricFlatModelInChart
    (g : SmoothRiemannianMetric I M) (x₀ : M) (y : E) :
    E →L[Real] E →L[Real] Real :=
  (trivializationAt (E →L[Real] E →L[Real] Real)
      (fun p : M => TangentSpace I p →L[Real] TangentSpace I p →L[Real] Real) x₀
      ⟨(extChartAt I x₀).symm y, g.inner ((extChartAt I x₀).symm y)⟩).2

private theorem metricFlatModelInChart_center_eq
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀) =
      (metricFlatContinuousEquiv (I := I) g x₀ :
        E →L[Real] (E →L[Real] Real)) := by
  have hcenter :
      (extChartAt I x₀).symm (extChartAt I x₀ x₀) = x₀ :=
    (extChartAt I x₀).left_inv (mem_extChartAt_source (I := I) x₀)
  ext v w
  simp only [metricFlatModelInChart]
  rw [hom_trivializationAt_apply]
  rw [hcenter]
  change
    (ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[Real] Real)
        (fun p : M => TangentSpace I p →L[Real] Real) x₀ x₀ x₀ x₀
        (g.inner x₀) v) w =
      ((metricFlatContinuousEquiv (I := I) g x₀) v) w
  have hxT :
      x₀ ∈ (trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet := by
    simp
  have hxDual :
      x₀ ∈ (trivializationAt (E →L[Real] Real)
          (fun p : M => TangentSpace I p →L[Real] Real) x₀).baseSet := by
    rw [hom_trivializationAt_baseSet]
    exact ⟨hxT, by simp⟩
  rw [ContinuousLinearMap.inCoordinates_eq hxT hxDual]
  simp [metricFlatContinuousEquiv, hom_trivializationAt,
    Trivialization.continuousLinearMap_apply]
  have hL :
      (trivializationAt E (TangentSpace I) x₀).symmL Real x₀ =
        (1 : E →L[Real] E) := by
    rw [TangentBundle.symmL_trivializationAt_eq_core
      (𝕜 := Real) (I := I) (b₀ := x₀) (b := x₀) (mem_chart_source H x₀)]
    ext z
    exact (tangentBundleCore I M).coordChange_self (achart H x₀) x₀
      (by rw [tangentBundleCore_baseSet, coe_achart]; exact mem_chart_source H x₀) z
  have hsymm (z : E) :
      (trivializationAt E (TangentSpace I) x₀).symm x₀ z = z := by
    change (trivializationAt E (TangentSpace I) x₀).symmL Real x₀ z = z
    rw [hL]
    rfl
  rw [hsymm v, hsymm w]
  rfl

private theorem metricFlatModelInChart_center_isInvertible
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀)).IsInvertible := by
  rw [metricFlatModelInChart_center_eq (I := I) g x₀]
  exact ContinuousLinearMap.isInvertible_equiv

/-- The fixed-chart metric flat map is smooth on the model chart at the center. -/
theorem metricFlatModelInChart_contDiffWithinAt
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    ContDiffWithinAt Real ∞
      (metricFlatModelInChart (I := I) g x₀)
      (Set.range I) (extChartAt I x₀ x₀) := by
  let e := trivializationAt (E →L[Real] E →L[Real] Real)
      (fun p : M => TangentSpace I p →L[Real] TangentSpace I p →L[Real] Real) x₀
  have hg :
      ContMDiffAt I
        (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) ∞
        (fun p : M =>
          (⟨p, g.inner p⟩ :
            TotalSpace (E →L[Real] E →L[Real] Real)
              (fun p : M =>
                TangentSpace I p →L[Real] TangentSpace I p →L[Real] Real)))
        x₀ :=
    (g.contMDiff.contMDiffAt (x := x₀)).of_le (by simp)
  have hcoord :
      ContMDiffAt I 𝓘(Real, E →L[Real] E →L[Real] Real) ∞
        (fun p : M => (e ⟨p, g.inner p⟩).2) x₀ := 
    by
      rw [contMDiffAt_totalSpace] at hg
      simpa [e] using hg.2
  have hsymm :
      ContMDiffWithinAt 𝓘(Real, E) I ∞ (extChartAt I x₀).symm
        (Set.range I) (extChartAt I x₀ x₀) := by
    simpa using
      contMDiffWithinAt_extChartAt_symm_range_self (I := I) (n := ∞) x₀
  have hcenter :
      (extChartAt I x₀).symm (extChartAt I x₀ x₀) = x₀ :=
    (extChartAt I x₀).left_inv (mem_extChartAt_source (I := I) x₀)
  have hcoord_center :
      ContMDiffAt I 𝓘(Real, E →L[Real] E →L[Real] Real) ∞
        (fun p : M => (e ⟨p, g.inner p⟩).2)
        ((extChartAt I x₀).symm (extChartAt I x₀ x₀)) := by
    simpa [hcenter] using hcoord
  have hcomp :
      ContMDiffWithinAt 𝓘(Real, E)
        𝓘(Real, E →L[Real] E →L[Real] Real) ∞
        ((fun p : M => (e ⟨p, g.inner p⟩).2) ∘ (extChartAt I x₀).symm)
        (Set.range I) (extChartAt I x₀ x₀) :=
    hcoord_center.comp_contMDiffWithinAt
      (x := extChartAt I x₀ x₀) hsymm
  exact hcomp.contDiffWithinAt

/-- The inverse metric flat map is smooth in the fixed model chart. -/
theorem inverseMetricFlatModelInChart_contDiffWithinAt
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    ContDiffWithinAt Real ∞
      (fun y : E =>
        ContinuousLinearMap.inverse
          (metricFlatModelInChart (I := I) g x₀ y))
      (Set.range I) (extChartAt I x₀ x₀) := by
  exact
    (metricFlatModelInChart_center_isInvertible (I := I) g x₀).contDiffAt_map_inverse
      |>.comp_contDiffWithinAt
        (x := extChartAt I x₀ x₀)
        (metricFlatModelInChart_contDiffWithinAt (I := I) g x₀)

/-- Fixed-chart inverse metric coefficients are smooth model functions. -/
theorem inverseMetricFlatModelInChart_component_contDiffWithinAt
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (k l : CoordinateIdx (𝕜 := Real) E) :
    ContDiffWithinAt Real ∞
      (fun y : E =>
        (Module.finBasis Real E).coord k
          ((ContinuousLinearMap.inverse
              (metricFlatModelInChart (I := I) g x₀ y))
            (LinearMap.toContinuousLinearMap
              ((Module.finBasis Real E).coord l))))
      (Set.range I) (extChartAt I x₀ x₀) := by
  let εl : E →L[Real] Real :=
    LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord l)
  let εk : E →L[Real] Real :=
    LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord k)
  have hinv := inverseMetricFlatModelInChart_contDiffWithinAt (I := I) g x₀
  have happ :
      ContDiffWithinAt Real ∞
        (fun y : E =>
          (ContinuousLinearMap.inverse
              (metricFlatModelInChart (I := I) g x₀ y)) εl)
        (Set.range I) (extChartAt I x₀ x₀) := by
    simpa [εl] using hinv.clm_apply contDiffWithinAt_const
  simpa [εk, εl] using (contDiffWithinAt_const (c := εk)).clm_apply happ

private theorem inverseMetricFlatModelInChart_component_center_eq_symm
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    (Module.finBasis Real E).coord i
        ((ContinuousLinearMap.inverse
            (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀)))
          (LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord j))) =
      (Module.finBasis Real E).coord j
        ((ContinuousLinearMap.inverse
            (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀)))
          (LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord i))) := by
  let A : E ≃L[Real] (E →L[Real] Real) := metricFlatContinuousEquiv (I := I) g x₀
  let ε : CoordinateIdx (𝕜 := Real) E -> E →L[Real] Real :=
    fun a => LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord a)
  have hInv :
      ContinuousLinearMap.inverse
          (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀)) =
        A.symm := by
    rw [metricFlatModelInChart_center_eq (I := I) g x₀]
    exact ContinuousLinearMap.inverse_equiv A
  rw [hInv]
  calc
    (Module.finBasis Real E).coord i (A.symm (ε j))
        = (ε i) (A.symm (ε j)) := rfl
    _ = (A (A.symm (ε i))) (A.symm (ε j)) := by
          rw [A.apply_symm_apply]
    _ = g.inner x₀ (A.symm (ε i)) (A.symm (ε j)) := by
          rw [metricFlatContinuousEquiv_apply]
    _ = g.inner x₀ (A.symm (ε j)) (A.symm (ε i)) := by
          exact g.symm x₀ (A.symm (ε i)) (A.symm (ε j))
    _ = (A (A.symm (ε j))) (A.symm (ε i)) := by
          rw [metricFlatContinuousEquiv_apply]
    _ = (ε j) (A.symm (ε i)) := by
          rw [A.apply_symm_apply]
    _ = (Module.finBasis Real E).coord j (A.symm (ε i)) := rfl

private theorem inverseMetricFlatModelInChart_metricInverseInBasis_center
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    MetricInverseInBasis (I := I) g x₀ (coordinateFrameAt_toBasis (I := I) x₀)
      (fun k l : CoordinateIdx (𝕜 := Real) E =>
        (Module.finBasis Real E).coord k
          ((ContinuousLinearMap.inverse
              (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀)))
            (LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord l)))) := by
  classical
  let A : E ≃L[Real] (E →L[Real] Real) := metricFlatContinuousEquiv (I := I) g x₀
  let ε : CoordinateIdx (𝕜 := Real) E -> E →L[Real] Real :=
    fun a => LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord a)
  let gInv : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
    fun k l =>
      (Module.finBasis Real E).coord k
        ((ContinuousLinearMap.inverse
            (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀))) (ε l))
  have hInv :
      ContinuousLinearMap.inverse
          (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀)) =
        A.symm := by
    rw [metricFlatModelInChart_center_eq (I := I) g x₀]
    exact ContinuousLinearMap.inverse_equiv A
  have hbasis :
      coordinateFrameAt_toBasis (I := I) x₀ = Module.finBasis Real E :=
    coordinateFrameAt_toBasis_eq_finBasis (I := I) x₀
  have hginv (k l : CoordinateIdx (𝕜 := Real) E) :
      gInv k l = (Module.finBasis Real E).coord k (A.symm (ε l)) := by
    dsimp [gInv]
    simpa [extChartAt] using
      congrArg (fun L : (E →L[Real] Real) →L[Real] E =>
        (Module.finBasis Real E).coord k (L (ε l))) hInv
  have hsym (k l : CoordinateIdx (𝕜 := Real) E) : gInv k l = gInv l k := by
    simp only [hginv]
    calc
      (Module.finBasis Real E).coord k (A.symm (ε l))
          = (ε k) (A.symm (ε l)) := rfl
      _ = (A (A.symm (ε k))) (A.symm (ε l)) := by
            rw [A.apply_symm_apply]
      _ = g.inner x₀ (A.symm (ε k)) (A.symm (ε l)) := by
            rw [metricFlatContinuousEquiv_apply]
      _ = g.inner x₀ (A.symm (ε l)) (A.symm (ε k)) := by
            exact g.symm x₀ (A.symm (ε k)) (A.symm (ε l))
      _ = (A (A.symm (ε l))) (A.symm (ε k)) := by
            rw [metricFlatContinuousEquiv_apply]
      _ = (ε l) (A.symm (ε k)) := by
            rw [A.apply_symm_apply]
      _ = (Module.finBasis Real E).coord l (A.symm (ε k)) := rfl
  have hsecond (i j : CoordinateIdx (𝕜 := Real) E) :
      (∑ k : CoordinateIdx (𝕜 := Real) E,
          g.inner x₀ ((coordinateFrameAt_toBasis (I := I) x₀) i)
            ((coordinateFrameAt_toBasis (I := I) x₀) k) * gInv k j) =
        (if i = j then 1 else 0) := by
    rw [hbasis]
    simp only [hginv]
    calc
      (∑ k : CoordinateIdx (𝕜 := Real) E,
          g.inner x₀ ((Module.finBasis Real E) i) ((Module.finBasis Real E) k) *
            (Module.finBasis Real E).coord k (A.symm (ε j)))
          = g.inner x₀ ((Module.finBasis Real E) i)
              (∑ k : CoordinateIdx (𝕜 := Real) E,
                (Module.finBasis Real E).coord k (A.symm (ε j)) •
                  (Module.finBasis Real E) k) := by
            rw [map_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            have hmap :=
              map_smul (g.inner x₀ ((Module.finBasis Real E) i))
                ((Module.finBasis Real E).coord k (A.symm (ε j)))
                ((Module.finBasis Real E) k)
            calc
              g.inner x₀ ((Module.finBasis Real E) i) ((Module.finBasis Real E) k) *
                  (Module.finBasis Real E).coord k (A.symm (ε j))
                  = (Module.finBasis Real E).coord k (A.symm (ε j)) *
                      g.inner x₀ ((Module.finBasis Real E) i)
                        ((Module.finBasis Real E) k) := by ring
              _ = (Module.finBasis Real E).coord k (A.symm (ε j)) •
                    g.inner x₀ ((Module.finBasis Real E) i)
                      ((Module.finBasis Real E) k) := by simp
              _ = g.inner x₀ ((Module.finBasis Real E) i)
                    ((Module.finBasis Real E).coord k (A.symm (ε j)) •
                      (Module.finBasis Real E) k) := hmap.symm
      _ = g.inner x₀ ((Module.finBasis Real E) i) (A.symm (ε j)) := by
            have hsum :
                (∑ k : CoordinateIdx (𝕜 := Real) E,
                  (Module.finBasis Real E).coord k (A.symm (ε j)) •
                    (Module.finBasis Real E) k) = A.symm (ε j) := by
              exact (Module.finBasis Real E).sum_repr (A.symm (ε j))
            exact congrArg (fun v => g.inner x₀ ((Module.finBasis Real E) i) v) hsum
      _ = g.inner x₀ (A.symm (ε j)) ((Module.finBasis Real E) i) := by
            exact g.symm x₀ ((Module.finBasis Real E) i) (A.symm (ε j))
      _ = (A (A.symm (ε j))) ((Module.finBasis Real E) i) := by
            rw [metricFlatContinuousEquiv_apply]
      _ = ε j ((Module.finBasis Real E) i) := by
            rw [A.apply_symm_apply]
      _ = (if i = j then 1 else 0) := by
            by_cases hij : i = j
            · subst hij
              simp [ε]
            · have hji : j ≠ i := by exact fun h => hij h.symm
              simp [ε, hji, hij]
  intro i j
  constructor
  · calc
      (∑ k : CoordinateIdx (𝕜 := Real) E,
          gInv i k * g.inner x₀ ((coordinateFrameAt_toBasis (I := I) x₀) k)
            ((coordinateFrameAt_toBasis (I := I) x₀) j))
          = ∑ k : CoordinateIdx (𝕜 := Real) E,
              g.inner x₀ ((coordinateFrameAt_toBasis (I := I) x₀) j)
                ((coordinateFrameAt_toBasis (I := I) x₀) k) * gInv k i := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [hsym i k, g.symm x₀ ((coordinateFrameAt_toBasis (I := I) x₀) k)
              ((coordinateFrameAt_toBasis (I := I) x₀) j)]
            ring
      _ = (if j = i then 1 else 0) := hsecond j i
      _ = (if i = j then 1 else 0) := by
            by_cases hij : i = j
            · subst hij
              simp
            · have hji : j ≠ i := fun h => hij h.symm
              simp [hij, hji]
  · exact hsecond i j

/-! ## Smooth Christoffel formula RHS in a fixed chart -/

/-- Fixed-chart metric coefficients as model functions. -/
noncomputable def metricFlatModelInChart_component
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j : CoordinateIdx (𝕜 := Real) E) (y : E) : Real :=
  metricFlatModelInChart (I := I) g x₀ y
    ((Module.finBasis Real E) i) ((Module.finBasis Real E) j)

/-- At the chart center, the fixed-chart metric component is the intrinsic
coordinate-frame metric component. -/
theorem metricFlatModelInChart_component_center
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    metricFlatModelInChart_component (I := I) g x₀ i j (extChartAt I x₀ x₀) =
      g.inner x₀ (coordinateFrameAt (I := I) x₀ i x₀)
        (coordinateFrameAt (I := I) x₀ j x₀) := by
  rw [metricFlatModelInChart_component, metricFlatModelInChart_center_eq]
  change ((metricFlatContinuousEquiv (I := I) g x₀)
      ((Module.finBasis Real E) i)) ((Module.finBasis Real E) j) =
    g.inner x₀ (coordinateFrameAt (I := I) x₀ i x₀)
      (coordinateFrameAt (I := I) x₀ j x₀)
  rw [metricFlatContinuousEquiv_apply]
  have hi : coordinateFrameAt (I := I) x₀ i x₀ = (Module.finBasis Real E) i := by
    rw [← coordinateFrameAt_toBasis_apply (I := I) x₀ i]
    rw [coordinateFrameAt_toBasis_eq_finBasis (I := I) x₀]
    rfl
  have hj : coordinateFrameAt (I := I) x₀ j x₀ = (Module.finBasis Real E) j := by
    rw [← coordinateFrameAt_toBasis_apply (I := I) x₀ j]
    rw [coordinateFrameAt_toBasis_eq_finBasis (I := I) x₀]
    rfl
  rw [hi, hj]

private theorem metricFlatModelInChart_component_eq_coord_component_comp_eventually_of_mem
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j : CoordinateIdx (𝕜 := Real) E) {y₀ : E}
    (hy₀ : y₀ ∈ (extChartAt I x₀).target) :
    metricFlatModelInChart_component (I := I) g x₀ i j
      =ᶠ[𝓝[Set.range I] y₀]
      fun y : E =>
        g.inner ((extChartAt I x₀).symm y)
          (coordinateFrameAt (I := I) x₀ i ((extChartAt I x₀).symm y))
          (coordinateFrameAt (I := I) x₀ j ((extChartAt I x₀).symm y)) := by
  filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem (I := I) hy₀] with y hy
  unfold metricFlatModelInChart_component metricFlatModelInChart
  rw [hom_trivializationAt_apply]
  change
    (ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[Real] Real)
        (fun p : M => TangentSpace I p →L[Real] Real) x₀
        ((extChartAt I x₀).symm y) x₀ ((extChartAt I x₀).symm y)
        (g.inner ((extChartAt I x₀).symm y))
        ((Module.finBasis Real E) i)) ((Module.finBasis Real E) j) =
      g.inner ((extChartAt I x₀).symm y)
        (coordinateFrameAt (I := I) x₀ i ((extChartAt I x₀).symm y))
        (coordinateFrameAt (I := I) x₀ j ((extChartAt I x₀).symm y))
  have hy_src : (extChartAt I x₀).symm y ∈ (chartAt H x₀).source := by
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I x₀).map_target hy
  have hy_base : (extChartAt I x₀).symm y ∈ coordinateFrameSet (I := I) x₀ := by
    simpa [coordinateFrameSet, coordinateTrivializationAt] using hy_src
  have hyT :
      (extChartAt I x₀).symm y ∈
        (trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet := by
    simpa [TangentBundle.trivializationAt_baseSet] using hy_src
  have hyDual :
      (extChartAt I x₀).symm y ∈
        (trivializationAt (E →L[Real] Real)
          (fun p : M => TangentSpace I p →L[Real] Real) x₀).baseSet := by
    rw [hom_trivializationAt_baseSet]
    exact ⟨hyT, by simp⟩
  rw [ContinuousLinearMap.inCoordinates_eq hyT hyDual]
  rw [Trivialization.coe_continuousLinearEquivAt_eq'
    (e := trivializationAt (E →L[Real] Real)
      (fun p : M => TangentSpace I p →L[Real] Real) x₀) (R := Real) hyDual]
  rw [Trivialization.symm_continuousLinearEquivAt_eq'
    (e := trivializationAt E (TangentSpace I : M -> Type _) x₀) (R := Real) hyT]
  simp only [ContinuousLinearMap.comp_apply]
  rw [coordinateFrameAt_apply_of_mem (I := I) hy_base i]
  rw [coordinateFrameAt_apply_of_mem (I := I) hy_base j]
  rw [(extChartAt I x₀).right_inv hy]
  rw [TangentBundle.symmL_trivializationAt (I := I) (𝕜 := Real) hy_src]
  rw [(extChartAt I x₀).right_inv hy]
  have hj_symm :
      (trivializationAt E (TangentSpace I : M -> Type _) x₀).symm
          ((extChartAt I x₀).symm y) ((Module.finBasis Real E) j) =
        (mfderivWithin 𝓘(Real, E) I (extChartAt I x₀).symm
          (Set.range I) y) ((Module.finBasis Real E) j) := by
    change (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real
        ((extChartAt I x₀).symm y) ((Module.finBasis Real E) j) =
      (mfderivWithin 𝓘(Real, E) I (extChartAt I x₀).symm
        (Set.range I) y) ((Module.finBasis Real E) j)
    rw [TangentBundle.symmL_trivializationAt (I := I) (𝕜 := Real) hy_src]
    rw [(extChartAt I x₀).right_inv hy]
    rfl
  change
      (((Trivialization.continuousLinearMap (RingHom.id Real)
          (trivializationAt E (TangentSpace I : M -> Type _) x₀)
          (trivializationAt Real (fun _ : M => Real) x₀)).toPretrivialization.linearMapAt Real
          ((extChartAt I x₀).symm y)
          ((g.inner ((extChartAt I x₀).symm y))
            ((mfderivWithin 𝓘(Real, E) I (extChartAt I x₀).symm
              (Set.range I) y) ((Module.finBasis Real E) i))))
        ((Module.finBasis Real E) j)) =
      g.inner ((extChartAt I x₀).symm y)
        ((mfderivWithin 𝓘(Real, E) I (extChartAt I x₀).symm
          (Set.range I) y) ((Module.finBasis Real E) i))
        ((mfderivWithin 𝓘(Real, E) I (extChartAt I x₀).symm
          (Set.range I) y) ((Module.finBasis Real E) j))
  rw [Pretrivialization.linearMapAt_apply]
  have hyDual' :
      (extChartAt I x₀).symm y ∈
        (Trivialization.continuousLinearMap (RingHom.id Real)
          (trivializationAt E (TangentSpace I : M -> Type _) x₀)
          (trivializationAt Real (fun _ : M => Real) x₀)).toPretrivialization.baseSet := by
    change (extChartAt I x₀).symm y ∈
      (trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet ∩
        (trivializationAt Real (fun _ : M => Real) x₀).baseSet
    exact ⟨hyT, by simp⟩
  rw [if_pos hyDual']
  change
      ((Trivialization.continuousLinearMap (RingHom.id Real)
          (trivializationAt E (TangentSpace I : M -> Type _) x₀)
          (trivializationAt Real (fun _ : M => Real) x₀)
        (⟨(extChartAt I x₀).symm y,
          (g.inner ((extChartAt I x₀).symm y))
            ((mfderivWithin 𝓘(Real, E) I (extChartAt I x₀).symm
              (Set.range I) y) ((Module.finBasis Real E) i))⟩ :
          TotalSpace (E →L[Real] Real)
            (fun p : M => TangentSpace I p →L[Real] Real))).2
        ((Module.finBasis Real E) j)) =
      g.inner ((extChartAt I x₀).symm y)
        ((mfderivWithin 𝓘(Real, E) I (extChartAt I x₀).symm
          (Set.range I) y) ((Module.finBasis Real E) i))
        ((mfderivWithin 𝓘(Real, E) I (extChartAt I x₀).symm
          (Set.range I) y) ((Module.finBasis Real E) j))
  rw [Bundle.Trivialization.continuousLinearMap_apply]
  simp [Trivial.trivialization, ContinuousLinearMap.comp_apply,
    Trivialization.linearMapAt_apply, Trivialization.symmL_apply]
  have hj_symm' :
      (trivializationAt E (TangentSpace I : M -> Type _) x₀).symm
          ((chartAt H x₀).symm (I.symm y)) ((Module.finBasis Real E) j) =
        (mfderivWithin 𝓘(Real, E) I ((chartAt H x₀).symm ∘ I.symm)
          (Set.range I) y) ((Module.finBasis Real E) j) := by
    simpa [extChartAt] using hj_symm
  rw [hj_symm']
  rfl

/-- Fixed-chart metric coefficients are smooth model functions. -/
theorem metricFlatModelInChart_component_contDiffWithinAt
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    ContDiffWithinAt Real ∞
      (metricFlatModelInChart_component (I := I) g x₀ i j)
      (Set.range I) (extChartAt I x₀ x₀) := by
  have h := metricFlatModelInChart_contDiffWithinAt (I := I) g x₀
  have hi :
      ContDiffWithinAt Real ∞
        (fun y : E =>
          metricFlatModelInChart (I := I) g x₀ y ((Module.finBasis Real E) i))
        (Set.range I) (extChartAt I x₀ x₀) := by
    simpa using h.clm_apply contDiffWithinAt_const
  simpa [metricFlatModelInChart_component] using hi.clm_apply contDiffWithinAt_const

/-- At the chart center, the model derivative of a fixed-chart metric coefficient
is the intrinsic directional derivative of the corresponding coordinate-frame
metric component. -/
theorem metricFlatModelInChart_component_deriv_center
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (a i j : CoordinateIdx (𝕜 := Real) E) :
    fderivWithin Real
        (metricFlatModelInChart_component (I := I) g x₀ i j)
        (Set.range I) (extChartAt I x₀ x₀) ((Module.finBasis Real E) a) =
      directionalDeriv (I := I) (coordinateFrameAt (I := I) x₀ a)
        (fun y : M =>
          g.inner y (coordinateFrameAt (I := I) x₀ i y)
            (coordinateFrameAt (I := I) x₀ j y)) x₀ := by
  let z₀ : E := extChartAt I x₀ x₀
  let f : M -> Real := fun y : M =>
    g.inner y (coordinateFrameAt (I := I) x₀ i y)
      (coordinateFrameAt (I := I) x₀ j y)
  have hzRange : z₀ ∈ Set.range I := by
    exact extChartAt_target_subset_range x₀ (mem_extChartAt_target (I := I) x₀)
  have heq :
      metricFlatModelInChart_component (I := I) g x₀ i j
        =ᶠ[𝓝[Set.range I] z₀]
        writtenInExtChartAt I 𝓘(Real, Real) x₀ f := by
    simpa [z₀, f, writtenInExtChartAt] using
      metricFlatModelInChart_component_eq_coord_component_comp_eventually_of_mem
        (I := I) g x₀ i j (mem_extChartAt_target (I := I) x₀)
  have hfd :
      fderivWithin Real
          (metricFlatModelInChart_component (I := I) g x₀ i j)
          (Set.range I) z₀ =
        fderivWithin Real
          (writtenInExtChartAt I 𝓘(Real, Real) x₀ f)
          (Set.range I) z₀ :=
    heq.fderivWithin_eq_of_mem hzRange
  have hf_md : MDifferentiableAt I 𝓘(Real, Real) f x₀ :=
    (metric_coordinateFrame_component_contMDiffAt (I := I) g x₀ i j).mdifferentiableAt
      (by simp)
  have hframe_center :
      coordinateFrameAt (I := I) x₀ a x₀ = (Module.finBasis Real E) a := by
    rw [← coordinateFrameAt_toBasis_apply (I := I) x₀ a]
    rw [coordinateFrameAt_toBasis_eq_finBasis (I := I) x₀]
    rfl
  unfold directionalDeriv extDerivFun
  change
    fderivWithin Real
        (metricFlatModelInChart_component (I := I) g x₀ i j)
        (Set.range I) z₀ ((Module.finBasis Real E) a) =
      (mfderiv I 𝓘(Real, Real) f x₀) (coordinateFrameAt (I := I) x₀ a x₀)
  rw [hframe_center, hf_md.mfderiv, hfd]
  rfl

/-- Fixed-chart coordinate derivatives of metric coefficients are smooth model
functions. -/
theorem metricFlatModelInChart_component_deriv_contDiffWithinAt
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (a i j : CoordinateIdx (𝕜 := Real) E) :
    ContDiffWithinAt Real ∞
      (fun y : E =>
        fderivWithin Real
          (metricFlatModelInChart_component (I := I) g x₀ i j)
          (Set.range I) y ((Module.finBasis Real E) a))
      (Set.range I) (extChartAt I x₀ x₀) := by
  have hf :=
    metricFlatModelInChart_component_contDiffWithinAt (I := I) g x₀ i j
  have hconst :
      ContDiffWithinAt Real ∞
        (fun _ : E => (Module.finBasis Real E) a)
        (Set.range I) (extChartAt I x₀ x₀) :=
    contDiffWithinAt_const
  exact hf.fderivWithin_right_apply hconst I.uniqueDiffOn (by simp)
    (extChartAt_target_subset_range x₀ (mem_extChartAt_target (I := I) x₀))

/-- The fixed-chart right hand side of the coordinate Christoffel formula. -/
noncomputable def leviCivitaChristoffelModelRHS
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j k : CoordinateIdx (𝕜 := Real) E) (y : E) : Real :=
  (1 / 2 : Real) *
    ∑ l : CoordinateIdx (𝕜 := Real) E,
      ((Module.finBasis Real E).coord k
        ((ContinuousLinearMap.inverse
            (metricFlatModelInChart (I := I) g x₀ y))
          (LinearMap.toContinuousLinearMap
            ((Module.finBasis Real E).coord l)))) *
        (fderivWithin Real
            (metricFlatModelInChart_component (I := I) g x₀ j l)
            (Set.range I) y ((Module.finBasis Real E) i) +
          fderivWithin Real
            (metricFlatModelInChart_component (I := I) g x₀ i l)
            (Set.range I) y ((Module.finBasis Real E) j) -
          fderivWithin Real
            (metricFlatModelInChart_component (I := I) g x₀ i j)
            (Set.range I) y ((Module.finBasis Real E) l))

/-- The fixed-chart right hand side of the Christoffel formula is smooth as a
model function. -/
theorem leviCivitaChristoffelModelRHS_contDiffWithinAt
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j k : CoordinateIdx (𝕜 := Real) E) :
    ContDiffWithinAt Real ∞
      (leviCivitaChristoffelModelRHS (I := I) g x₀ i j k)
      (Set.range I) (extChartAt I x₀ x₀) := by
  classical
  unfold leviCivitaChristoffelModelRHS
  refine contDiffWithinAt_const.mul ?_
  refine ContDiffWithinAt.sum fun l _ => ?_
  have hinv :=
    inverseMetricFlatModelInChart_component_contDiffWithinAt (I := I) g x₀ k l
  have h₁ :=
    metricFlatModelInChart_component_deriv_contDiffWithinAt (I := I) g x₀ i j l
  have h₂ :=
    metricFlatModelInChart_component_deriv_contDiffWithinAt (I := I) g x₀ j i l
  have h₃ :=
    metricFlatModelInChart_component_deriv_contDiffWithinAt (I := I) g x₀ l i j
  exact hinv.mul ((h₁.add h₂).sub h₃)

/-- At the chart center, the smooth model Christoffel RHS recovers the
coordinate Christoffel coefficient of the Koszul Levi-Civita connection. -/
theorem leviCivitaChristoffelModelRHS_center_eq_christoffel
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j k : CoordinateIdx (𝕜 := Real) E) :
    leviCivitaChristoffelModelRHS (I := I) g x₀ i j k (extChartAt I x₀ x₀) =
      christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) g)
        (coordinateFrameAt (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀) x₀ i j k := by
  classical
  let gInv : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
    fun k l =>
      (Module.finBasis Real E).coord k
        ((ContinuousLinearMap.inverse
            (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀)))
          (LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord l)))
  have hinv : MetricInverseInBasis (I := I) g x₀
      (coordinateFrameAt_toBasis (I := I) x₀) gInv :=
    inverseMetricFlatModelInChart_metricInverseInBasis_center (I := I) g x₀
  have hformula :=
    RicciFlower.LeviCivita.leviCivitaConnectionOfMetric_coordinate_christoffel_formula
      (I := I) g x₀ gInv hinv i j k
  rw [hformula]
  unfold leviCivitaChristoffelModelRHS
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  dsimp [gInv]
  congr 1
  ·
    have h₁ :
        fderivWithin Real (metricFlatModelInChart_component (I := I) g x₀ j l)
            (Set.range I) (I ((chartAt H x₀) x₀)) ((Module.finBasis Real E) i) =
          directionalDeriv (I := I) (coordinateFrameAt (I := I) x₀ i)
            (fun y : M =>
              g.inner y (coordinateFrameAt (I := I) x₀ j y)
                (coordinateFrameAt (I := I) x₀ l y)) x₀ := by
        simpa [extChartAt] using
          metricFlatModelInChart_component_deriv_center (I := I) g x₀ i j l
    have h₂ :
        fderivWithin Real (metricFlatModelInChart_component (I := I) g x₀ i l)
            (Set.range I) (I ((chartAt H x₀) x₀)) ((Module.finBasis Real E) j) =
          directionalDeriv (I := I) (coordinateFrameAt (I := I) x₀ j)
            (fun y : M =>
              g.inner y (coordinateFrameAt (I := I) x₀ i y)
                (coordinateFrameAt (I := I) x₀ l y)) x₀ := by
        simpa [extChartAt] using
          metricFlatModelInChart_component_deriv_center (I := I) g x₀ j i l
    have h₃ :
        fderivWithin Real (metricFlatModelInChart_component (I := I) g x₀ i j)
            (Set.range I) (I ((chartAt H x₀) x₀)) ((Module.finBasis Real E) l) =
          directionalDeriv (I := I) (coordinateFrameAt (I := I) x₀ l)
            (fun y : M =>
              g.inner y (coordinateFrameAt (I := I) x₀ i y)
                (coordinateFrameAt (I := I) x₀ j y)) x₀ := by
        simpa [extChartAt] using
          metricFlatModelInChart_component_deriv_center (I := I) g x₀ l i j
    rw [h₁, h₂, h₃]

end LeviCivita
end RicciFlower

