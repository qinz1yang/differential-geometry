import RicciFlower.Coordinates.Normal.SmoothFlow.Jet

/-!
# Generic C1 flow dependence layer

This module contains the model-independent C1 error, Taylor residual, and
Gronwall estimates used by the normal-coordinate variational flow.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RicciFlower
namespace Coordinates

open Bundle Filter
open scoped Manifold ContDiff Topology Uniformity
open RicciFlower.GlobalGeometry.Lecture07

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [VectorBundle Real E (TangentSpace I : M -> Type _)]
variable [SigmaCompactSpace M] [T2Space M]

/-- The coefficient of the forcing term in `gronwallBound 0 K ε t`. -/
private def gronwallCoeff (K t : Real) : Real :=
  if K = 0 then t else (Real.exp (K * t) - 1) / K

private theorem gronwallBound_zero_eq_mul (K ε t : Real) :
    gronwallBound 0 K ε t = ε * gronwallCoeff K t := by
  by_cases hK : K = 0
  · subst K
    simp [gronwallBound, gronwallCoeff]
  · simp [gronwallBound, gronwallCoeff, hK, div_eq_mul_inv]
    ring

/-- If the Taylor-residual coefficient tends to zero, then the corresponding
Gronwall forcing term is little-o in the perturbation. -/
private theorem gronwall_forcing_isLittleO
    {X : Type*} [NormedAddCommGroup X] {l : Filter X}
    {C : X -> Real} {B L T : Real}
    (hC : Tendsto C l (𝓝 0)) :
    (fun h : X => gronwallBound 0 B (C h * (L * ‖h‖)) T)
      =o[l] (fun h : X => h) := by
  refine Asymptotics.IsLittleO.of_bound ?_
  intro c hc
  let A : Real := |L| * |gronwallCoeff B T| + 1
  have hApos : 0 < A := by
    dsimp [A]
    positivity
  have hsmall : ∀ᶠ h in l, |C h| ≤ c / A := by
    have hAbs : Tendsto (fun h : X => |C h|) l (𝓝 0) := by
      simpa using (continuous_abs.tendsto (0 : Real)).comp hC
    have hball :=
      hAbs.eventually (Metric.ball_mem_nhds (0 : Real) (div_pos hc hApos))
    filter_upwards [hball] with h hh
    have hlt : |C h| < c / A := by
      simpa [Real.dist_eq, abs_of_nonneg (abs_nonneg (C h))] using hh
    exact le_of_lt hlt
  filter_upwards [hsmall] with h hh
  have hnorm : 0 ≤ ‖h‖ := norm_nonneg _
  have hP_nonneg : 0 ≤ |L| * |gronwallCoeff B T| := by positivity
  have hP_le_A : |L| * |gronwallCoeff B T| ≤ A := by
    dsimp [A]
    linarith
  have hdiv_nonneg : 0 ≤ c / A := by positivity
  have hcoef :
      (c / A) * (|L| * |gronwallCoeff B T|) ≤ c := by
    calc
      (c / A) * (|L| * |gronwallCoeff B T|)
          ≤ (c / A) * A := by
            exact mul_le_mul_of_nonneg_left hP_le_A hdiv_nonneg
      _ = c := by
        field_simp [ne_of_gt hApos]
  calc
    ‖gronwallBound 0 B (C h * (L * ‖h‖)) T‖
        = |C h| * (|L| * |gronwallCoeff B T|) * ‖h‖ := by
          rw [gronwallBound_zero_eq_mul]
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg hnorm]
          ring
    _ ≤ (c / A) * (|L| * |gronwallCoeff B T|) * ‖h‖ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hh hP_nonneg) hnorm
    _ ≤ c * ‖h‖ := by
          exact mul_le_mul_of_nonneg_right hcoef hnorm

/-- Turn a Gronwall forcing bound with a vanishing coefficient into a little-o
estimate for a vector-valued error. -/
private theorem isLittleO_of_gronwall_bound
    {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    {l : Filter X} {f : X -> Y} {C : X -> Real} {B L T : Real}
    (hC : Tendsto C l (𝓝 0))
    (hbound : ∀ᶠ h in l,
      ‖f h‖ ≤ gronwallBound 0 B (C h * (L * ‖h‖)) T) :
    f =o[l] (fun h : X => h) := by
  have hg :=
    gronwall_forcing_isLittleO (X := X) (l := l)
      (C := C) (B := B) (L := L) (T := T) hC
  refine Asymptotics.IsLittleO.of_bound ?_
  intro c hc
  filter_upwards [hbound, hg.bound hc] with h hf hg'
  exact hf.trans ((le_abs_self _).trans hg')

/-- A variant of `isLittleO_of_gronwall_bound` avoiding a chosen residual
coefficient: an eventual Gronwall bound with every positive constant is enough. -/
theorem isLittleO_of_gronwall_bound_eventually
    {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    {l : Filter X} {f : X -> Y} {B L T : Real}
    (hbound : ∀ η > 0, ∀ᶠ h in l,
      ‖f h‖ ≤ gronwallBound 0 B (η * (L * ‖h‖)) T) :
    f =o[l] (fun h : X => h) := by
  refine Asymptotics.IsLittleO.of_bound ?_
  intro c hc
  let A : Real := |L| * |gronwallCoeff B T| + 1
  have hApos : 0 < A := by
    dsimp [A]
    positivity
  let η : Real := c / A
  have hηpos : 0 < η := by
    dsimp [η]
    positivity
  have hP_nonneg : 0 ≤ |L| * |gronwallCoeff B T| := by positivity
  have hP_le_A : |L| * |gronwallCoeff B T| ≤ A := by
    dsimp [A]
    linarith
  have hη_nonneg : 0 ≤ η := le_of_lt hηpos
  have hcoef : η * (|L| * |gronwallCoeff B T|) ≤ c := by
    calc
      η * (|L| * |gronwallCoeff B T|) ≤ η * A := by
        exact mul_le_mul_of_nonneg_left hP_le_A hη_nonneg
      _ = c := by
        dsimp [η, A]
        field_simp [ne_of_gt hApos]
  filter_upwards [hbound η hηpos] with h hf
  have hnorm : 0 ≤ ‖h‖ := norm_nonneg _
  have hgr :
      ‖gronwallBound 0 B (η * (L * ‖h‖)) T‖
        = η * (|L| * |gronwallCoeff B T|) * ‖h‖ := by
    rw [gronwallBound_zero_eq_mul]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg hη_nonneg,
      abs_of_nonneg hnorm]
    ring
  calc
    ‖f h‖ ≤ gronwallBound 0 B (η * (L * ‖h‖)) T := hf
    _ ≤ ‖gronwallBound 0 B (η * (L * ‖h‖)) T‖ := le_abs_self _
    _ = η * (|L| * |gronwallCoeff B T|) * ‖h‖ := hgr
    _ ≤ c * ‖h‖ := by
      exact mul_le_mul_of_nonneg_right hcoef hnorm

section GenericC1Flow

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace Real X]

/-- Error between a flow endpoint at `z + h` and the first-order variational
approximation at `z`.  This is the model-independent core of the C1
flow-dependence proof. -/
def flowError
    (Φ : X -> Real -> X) (A : X -> Real -> X →L[Real] X)
    (z h : X) (t : Real) : X :=
  Φ (z + h) t - Φ z t - A z t h

/-- Raw right-hand side of the model-independent variational error equation. -/
def flowErrorRHS
    (F : X -> X) (Φ : X -> Real -> X) (A : X -> Real -> X →L[Real] X)
    (z h : X) (t : Real) : X :=
  F (Φ (z + h) t) - F (Φ z t) -
    fderiv Real F (Φ z t) (A z t h)

/-- Taylor-residual part of the model-independent variational error equation. -/
def flowTaylorRem
    (F : X -> X) (Φ : X -> Real -> X)
    (z h : X) (t : Real) : X :=
  F (Φ (z + h) t) - F (Φ z t) -
    fderiv Real F (Φ z t) (Φ (z + h) t - Φ z t)

/-- Generic augmented vector field for a parameterized first variational
equation of `z' = F z`.  The second component is a linear map from an external
parameter space into the state space. -/
def paramVariationalRHS
    {P : Type*} [NormedAddCommGroup P] [NormedSpace Real P]
    (F : X -> X) (p : X × (P →L[Real] X)) : X × (P →L[Real] X) :=
  (F p.1, (fderiv Real F p.1).comp p.2)

@[simp] theorem paramVariationalRHS_fst
    {P : Type*} [NormedAddCommGroup P] [NormedSpace Real P]
    (F : X -> X) (p : X × (P →L[Real] X)) :
    (paramVariationalRHS F p).1 = F p.1 := rfl

@[simp] theorem paramVariationalRHS_snd
    {P : Type*} [NormedAddCommGroup P] [NormedSpace Real P]
    (F : X -> X) (p : X × (P →L[Real] X)) :
    (paramVariationalRHS F p).2 = (fderiv Real F p.1).comp p.2 := rfl

/-- Smoothness of the generic parameterized variational RHS follows from
smoothness of the base RHS. -/
theorem paramVariationalRHS_contDiffAt
    {P : Type*} [NormedAddCommGroup P] [NormedSpace Real P]
    {F : X -> X} {z : X} {A : P →L[Real] X}
    (hF : ContDiffAt Real ∞ F z) :
    ContDiffAt Real ∞ (paramVariationalRHS (P := P) F) (z, A) := by
  let L := P →L[Real] X
  let p0 : X × L := (z, A)
  have hF' :
      ContDiffAt Real ∞ (fun p : X × L => F p.1) p0 := by
    exact hF.comp p0 contDiffAt_fst
  have hDF0 : ContDiffAt Real ∞ (fderiv Real F) z := by
    exact hF.fderiv_right (m := ∞) (by rw [ENat.coe_top_add_one])
  have hDF :
      ContDiffAt Real ∞ (fun p : X × L => fderiv Real F p.1) p0 := by
    exact hDF0.comp p0 contDiffAt_fst
  have hA : ContDiffAt Real ∞ (fun p : X × L => p.2) p0 :=
    contDiffAt_snd
  have hcomp :
      ContDiffAt Real ∞
        (fun p : X × L => (fderiv Real F p.1).comp p.2) p0 := by
    exact hDF.clm_comp hA
  simpa [paramVariationalRHS, p0, L] using hF'.prodMk hcomp

/-- Generic augmented vector field for the first variational equation of
`z' = F z` with parameter space equal to the state space. -/
def variationalRHS
    (F : X -> X) (p : X × (X →L[Real] X)) : X × (X →L[Real] X) :=
  paramVariationalRHS (P := X) F p

@[simp] theorem variationalRHS_fst
    (F : X -> X) (p : X × (X →L[Real] X)) :
    (variationalRHS F p).1 = F p.1 := rfl

@[simp] theorem variationalRHS_snd
    (F : X -> X) (p : X × (X →L[Real] X)) :
    (variationalRHS F p).2 = (fderiv Real F p.1).comp p.2 := rfl

/-- Smoothness of the generic augmented variational RHS follows from
smoothness of the base RHS. -/
theorem variationalRHS_contDiffAt
    {F : X -> X} {z : X} {A : X →L[Real] X}
    (hF : ContDiffAt Real ∞ F z) :
    ContDiffAt Real ∞ (variationalRHS F) (z, A) :=
  paramVariationalRHS_contDiffAt (P := X) hF

/-- Base endpoint of a controlled augmented variational flow. -/
def controlledBaseEndpoint
    (Ψ : X × (X →L[Real] X) -> Real -> X × (X →L[Real] X))
    (b : Real) (z : X) : X :=
  (Ψ (z, ContinuousLinearMap.id Real X) b).1

/-- Linear endpoint of a controlled augmented variational flow. -/
def controlledDerivEndpoint
    (Ψ : X × (X →L[Real] X) -> Real -> X × (X →L[Real] X))
    (b : Real) (z : X) : X →L[Real] X :=
  (Ψ (z, ContinuousLinearMap.id Real X) b).2

/-- The base component of a generic augmented flow solves the original ODE. -/
theorem controlledBase_hasDerivWithinAt
    {F : X -> X}
    {Ψ : X × (X →L[Real] X) -> Real -> X × (X →L[Real] X)}
    {z : X} {s : Set Real} {t : Real}
    (hΨ :
      HasDerivWithinAt
        (Ψ (z, ContinuousLinearMap.id Real X))
        (variationalRHS F (Ψ (z, ContinuousLinearMap.id Real X) t)) s t) :
    HasDerivWithinAt
      (controlledBaseEndpoint Ψ · z)
      (F (controlledBaseEndpoint Ψ t z)) s t := by
  let L := X →L[Real] X
  let A : L := ContinuousLinearMap.id Real X
  have hfst :
      HasFDerivWithinAt (fun q : X × L => q.1)
        (ContinuousLinearMap.fst Real X L) Set.univ
        (Ψ (z, A) t) :=
    (hasFDerivAt_fst (𝕜 := Real) (E := X) (F := L)
      (p := Ψ (z, A) t)).hasFDerivWithinAt
  have hmaps : Set.MapsTo (Ψ (z, A)) s Set.univ := by
    intro y hy
    trivial
  have hcomp := hfst.comp_hasDerivWithinAt t hΨ hmaps
  simpa [Function.comp_def, controlledBaseEndpoint, variationalRHS, L, A]
    using hcomp

/-- The linear component of a generic augmented flow solves the variational
equation. -/
theorem controlledDeriv_hasDerivWithinAt
    {F : X -> X}
    {Ψ : X × (X →L[Real] X) -> Real -> X × (X →L[Real] X)}
    {z : X} {s : Set Real} {t : Real}
    (hΨ :
      HasDerivWithinAt
        (Ψ (z, ContinuousLinearMap.id Real X))
        (variationalRHS F (Ψ (z, ContinuousLinearMap.id Real X) t)) s t) :
    HasDerivWithinAt
      (controlledDerivEndpoint Ψ · z)
      ((fderiv Real F (controlledBaseEndpoint Ψ t z)).comp
        (controlledDerivEndpoint Ψ t z)) s t := by
  let L := X →L[Real] X
  let A : L := ContinuousLinearMap.id Real X
  have hsnd :
      HasFDerivWithinAt (fun q : X × L => q.2)
        (ContinuousLinearMap.snd Real X L) Set.univ
        (Ψ (z, A) t) :=
    (hasFDerivAt_snd (𝕜 := Real) (E := X) (F := L)
      (p := Ψ (z, A) t)).hasFDerivWithinAt
  have hmaps : Set.MapsTo (Ψ (z, A)) s Set.univ := by
    intro y hy
    trivial
  have hcomp := hsnd.comp_hasDerivWithinAt t hΨ hmaps
  simpa [Function.comp_def, controlledBaseEndpoint, controlledDerivEndpoint,
    variationalRHS, L, A] using hcomp

/-- Pointwise Taylor-residual estimate for a generic vector field on a convex
set. -/
theorem flowTaylorRem_norm_le
    {F : X -> X} {Φ : X -> Real -> X}
    (z h : X) (t : Real)
    {s : Set X} (hs : Convex Real s)
    (hFdiff : ∀ q ∈ s, DifferentiableAt Real F q)
    (hz : Φ z t ∈ s)
    (hzh : Φ (z + h) t ∈ s)
    {C : Real}
    (hD : ∀ u ∈ s,
      ‖fderiv Real F u - fderiv Real F (Φ z t)‖ ≤ C) :
    ‖flowTaylorRem F Φ z h t‖ ≤ C * ‖Φ (z + h) t - Φ z t‖ := by
  have hCalc :
      ‖F (Φ (z + h) t) - F (Φ z t) -
          (fderiv Real F (Φ z t)) ((Φ (z + h) t) - Φ z t)‖
        ≤ C * ‖(Φ (z + h) t) - Φ z t‖ := by
    refine hs.norm_image_sub_le_of_norm_hasFDerivWithin_le'
      (f := F) (f' := fun q => fderiv Real F q)
      (φ := fderiv Real F (Φ z t)) ?_ ?_ hz hzh
    · intro q hq
      exact ((hFdiff q hq).hasFDerivAt).hasFDerivWithinAt
    · intro q hq
      exact hD q hq
  simpa [flowTaylorRem] using hCalc

/-- Lipschitz dependence of an augmented flow controls separation of its base
endpoints. -/
theorem controlledBase_dist_le_of_lipschitz
    {x0 z h : X}
    {Ψ : X × (X →L[Real] X) -> Real -> X × (X →L[Real] X)}
    {r L' : NNReal} {t : Real}
    (hLip :
      LipschitzOnWith L'
        (fun p => Ψ p t)
        (Metric.closedBall (x0, ContinuousLinearMap.id Real X) r))
    (hz :
      (z, ContinuousLinearMap.id Real X) ∈
        Metric.closedBall (x0, ContinuousLinearMap.id Real X) r)
    (hzh :
      (z + h, ContinuousLinearMap.id Real X) ∈
        Metric.closedBall (x0, ContinuousLinearMap.id Real X) r) :
    dist (controlledBaseEndpoint Ψ t (z + h))
      (controlledBaseEndpoint Ψ t z) ≤ (L' : Real) * ‖h‖ := by
  let L := X →L[Real] X
  let idLin : L := ContinuousLinearMap.id Real X
  let pzh : X × L := (z + h, idLin)
  let pz : X × L := (z, idLin)
  have hdist := hLip.dist_le_mul pzh hzh pz hz
  have hfst :
      dist (controlledBaseEndpoint Ψ t (z + h))
        (controlledBaseEndpoint Ψ t z) ≤ dist (Ψ pzh t) (Ψ pz t) := by
    change dist (Ψ pzh t).1 (Ψ pz t).1 ≤ dist (Ψ pzh t) (Ψ pz t)
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have hpdist : dist pzh pz = ‖h‖ := by
    have hzdist : dist (z + h) z = ‖h‖ := by
      rw [dist_eq_norm]
      have hsub : z + h - z = h := by
        abel
      rw [hsub]
    simp [pzh, pz, idLin, dist_prod_same_right, hzdist]
  exact hfst.trans (by simpa [hpdist] using hdist)

/-- Uniform continuity of `D F` in a tube around a compact base trajectory. -/
theorem fderiv_uniform_tube
    {F : X -> X} {K : Set Real} (hK : IsCompact K)
    {γ : Real -> X}
    (hγ : ContinuousOn γ K)
    (hDcont : ∀ y ∈ γ '' K, ContinuousAt (fderiv Real F) y) :
    ∀ c > 0, ∃ δ > 0, ∀ t ∈ K, ∀ u : X,
      dist u (γ t) < δ ->
        ‖fderiv Real F u - fderiv Real F (γ t)‖ ≤ c := by
  intro c hc
  let D : X -> (X →L[Real] X) := fderiv Real F
  have hcomp : IsCompact (γ '' K) :=
    hK.image_of_continuousOn hγ
  have hU :
      {p : X × X |
        p.1 ∈ γ '' K ->
          (D p.1, D p.2) ∈
            {q : (X →L[Real] X) × (X →L[Real] X) |
              dist q.1 q.2 < c}} ∈ 𝓤 X :=
    hcomp.uniformContinuousAt_of_continuousAt D hDcont
      (Metric.dist_mem_uniformity hc)
  rcases Metric.mem_uniformity_dist.mp hU with ⟨δ, hδ, hδsub⟩
  refine ⟨δ, hδ, ?_⟩
  intro t ht u hu
  have hpair :
      ((γ t, u) : X × X) ∈
        {p : X × X |
          p.1 ∈ γ '' K ->
            (D p.1, D p.2) ∈
              {q : (X →L[Real] X) × (X →L[Real] X) |
                dist q.1 q.2 < c}} :=
    hδsub (by simpa [dist_comm] using hu)
  have hγmem : γ t ∈ γ '' K := ⟨t, ht, rfl⟩
  have hdist : dist (D (γ t)) (D u) < c := hpair hγmem
  have hnorm : ‖D u - D (γ t)‖ < c := by
    have hdist' : dist (D u) (D (γ t)) < c := by
      simpa [dist_comm] using hdist
    simpa [D, dist_eq_norm] using hdist'
  simpa [D] using le_of_lt hnorm

/-- The derivative of a vector field is bounded along a compact continuous
base trajectory if it is continuous along that trajectory. -/
theorem fderiv_bound_on_base
    {F : X -> X} {γ : Real -> X} {b : Real}
    (hγ : ContinuousOn γ (Set.Icc (0 : Real) b))
    (hDcont :
      ∀ y ∈ γ '' Set.Icc (0 : Real) b,
        ContinuousAt (fderiv Real F) y) :
    ∃ B : Real, ∀ t ∈ Set.Icc (0 : Real) b,
      ‖fderiv Real F (γ t)‖ ≤ B := by
  have hDF :
      ContinuousOn (fun t : Real => fderiv Real F (γ t))
        (Set.Icc (0 : Real) b) := by
    intro t ht
    exact (hDcont (γ t) ⟨t, ht, rfl⟩).comp_continuousWithinAt
      (hγ.continuousWithinAt ht)
  exact isCompact_Icc.exists_bound_of_continuousOn hDF

/-- Lipschitz control of an augmented flow turns uniform continuity of `D F`
around the base trajectory into a derivative-difference estimate on trajectory
segments. -/
theorem controlled_fderiv_segment_small_of_lipschitz
    {F : X -> X} {x0 z : X}
    {Ψ : X × (X →L[Real] X) -> Real -> X × (X →L[Real] X)}
    {r L' : NNReal} {b : Real}
    (hbase :
      ContinuousOn (fun t : Real => controlledBaseEndpoint Ψ t z)
        (Set.Icc (0 : Real) b))
    (hDcont :
      ∀ y ∈ (fun t : Real => controlledBaseEndpoint Ψ t z) ''
          Set.Icc (0 : Real) b,
        ContinuousAt (fderiv Real F) y)
    (hLip : ∀ t ∈ Set.Ico (0 : Real) b,
      LipschitzOnWith L'
        (fun p => Ψ p t)
        (Metric.closedBall (x0, ContinuousLinearMap.id Real X) r))
    (hz0 :
      (z, ContinuousLinearMap.id Real X) ∈
        Metric.closedBall (x0, ContinuousLinearMap.id Real X) r) :
    ∀ η > 0, ∃ ρ > 0, ∀ h : X,
      (L' : Real) * ‖h‖ < ρ ->
      (z + h, ContinuousLinearMap.id Real X) ∈
        Metric.closedBall (x0, ContinuousLinearMap.id Real X) r ->
      ∀ t ∈ Set.Ico (0 : Real) b,
      ∀ u ∈ segment Real
          (controlledBaseEndpoint Ψ t z)
          (controlledBaseEndpoint Ψ t (z + h)),
        ‖fderiv Real F u -
          fderiv Real F (controlledBaseEndpoint Ψ t z)‖ ≤ η := by
  intro η hη
  obtain ⟨ρ, hρ, hρsmall⟩ :=
    fderiv_uniform_tube (F := F)
      (K := Set.Icc (0 : Real) b) isCompact_Icc
      (γ := fun t : Real => controlledBaseEndpoint Ψ t z)
      hbase hDcont η hη
  refine ⟨ρ, hρ, ?_⟩
  intro h hsmall hzh0 t ht u hu
  have htcc : t ∈ Set.Icc (0 : Real) b :=
    Set.Ico_subset_Icc_self ht
  have hsep :=
    controlledBase_dist_le_of_lipschitz
      (x0 := x0) (Ψ := Ψ) (r := r) (L' := L') (z := z) (h := h)
      (t := t) (hLip t ht) hz0 hzh0
  have hudist :
      dist u (controlledBaseEndpoint Ψ t z) <
        ρ := by
    have hball :
        u ∈ Metric.closedBall (controlledBaseEndpoint Ψ t z)
          (dist (controlledBaseEndpoint Ψ t z)
            (controlledBaseEndpoint Ψ t (z + h))) :=
      segment_subset_closedBall_left
        (controlledBaseEndpoint Ψ t z)
        (controlledBaseEndpoint Ψ t (z + h)) hu
    have hudist_le :
        dist u (controlledBaseEndpoint Ψ t z) ≤
          dist (controlledBaseEndpoint Ψ t z)
            (controlledBaseEndpoint Ψ t (z + h)) := by
      simpa [Metric.mem_closedBall] using hball
    have hsep' :
        dist (controlledBaseEndpoint Ψ t z)
            (controlledBaseEndpoint Ψ t (z + h)) ≤
          (L' : Real) * ‖h‖ := by
      simpa [dist_comm] using hsep
    exact lt_of_le_of_lt (hudist_le.trans hsep') hsmall
  exact hρsmall t htcc u hudist

/-- The previous segment estimate gives the Taylor-residual forcing estimate
needed by the generic controlled C1 theorem. -/
theorem controlledTaylorRem_eventually_of_lipschitz
    {F : X -> X} {x0 z : X}
    {Ψ : X × (X →L[Real] X) -> Real -> X × (X →L[Real] X)}
    {r L' : NNReal} {b : Real}
    (hFdiff : ∀ q : X, DifferentiableAt Real F q)
    (hbase :
      ContinuousOn (fun t : Real => controlledBaseEndpoint Ψ t z)
        (Set.Icc (0 : Real) b))
    (hDcont :
      ∀ y ∈ (fun t : Real => controlledBaseEndpoint Ψ t z) ''
          Set.Icc (0 : Real) b,
        ContinuousAt (fderiv Real F) y)
    (hLip : ∀ t ∈ Set.Ico (0 : Real) b,
      LipschitzOnWith L'
        (fun p => Ψ p t)
        (Metric.closedBall (x0, ContinuousLinearMap.id Real X) r))
    (hzopen :
      (z, ContinuousLinearMap.id Real X) ∈
        Metric.ball (x0, ContinuousLinearMap.id Real X) r) :
    ∀ η > 0, ∀ᶠ h : X in 𝓝 0,
      ∀ t ∈ Set.Ico (0 : Real) b,
        ‖flowTaylorRem F (fun y τ => controlledBaseEndpoint Ψ τ y) z h t‖ ≤
          η * ((L' : Real) * ‖h‖) := by
  let idLin : X →L[Real] X := ContinuousLinearMap.id Real X
  have hz0 :
      (z, idLin) ∈ Metric.closedBall (x0, ContinuousLinearMap.id Real X) r := by
    exact Metric.ball_subset_closedBall (by simpa [idLin] using hzopen)
  have hDsmall :=
    controlled_fderiv_segment_small_of_lipschitz
      (F := F) (x0 := x0) (z := z) (Ψ := Ψ)
      (r := r) (L' := L') (b := b)
      hbase hDcont hLip (by simpa [idLin] using hz0)
  have hinit_cont :
      ContinuousAt (fun h : X => (z + h, idLin)) 0 := by
    have hleft : ContinuousAt (fun h : X => z + h) 0 := by
      simpa using (continuousAt_const.add continuousAt_id :
        ContinuousAt (fun h : X => z + h) 0)
    exact hleft.prodMk_nhds continuousAt_const
  have hzh_eventually :
      ∀ᶠ h : X in 𝓝 0,
        (z + h, idLin) ∈
          Metric.closedBall (x0, ContinuousLinearMap.id Real X) r := by
    have hzopen0 :
        (fun h : X => (z + h, idLin)) 0 ∈
            Metric.ball (x0, ContinuousLinearMap.id Real X) r := by
      simpa [idLin] using hzopen
    filter_upwards
      [hinit_cont.eventually (Metric.isOpen_ball.mem_nhds hzopen0)] with h hh
    exact Metric.ball_subset_closedBall hh
  intro η hη
  obtain ⟨ρ, hρ, hρsmall⟩ := hDsmall η hη
  have hmul_cont :
      Continuous (fun h : X => (L' : Real) * ‖h‖) :=
    continuous_const.mul continuous_norm
  have hsmall_eventually :
      ∀ᶠ h : X in 𝓝 0, (L' : Real) * ‖h‖ < ρ := by
    have hball :=
      (hmul_cont.continuousAt (x := (0 : X))).eventually
        (Metric.ball_mem_nhds ((L' : Real) * ‖(0 : X)‖) hρ)
    filter_upwards [hball] with h hh
    have habs : |(L' : Real) * ‖h‖| < ρ := by
      simpa [Real.dist_eq] using hh
    exact (abs_lt.1 habs).2
  filter_upwards [hzh_eventually, hsmall_eventually] with h hzh0 hsmall
  intro t ht
  let s : Set X :=
    segment Real (controlledBaseEndpoint Ψ t z)
      (controlledBaseEndpoint Ψ t (z + h))
  have hD : ∀ u ∈ s,
      ‖fderiv Real F u -
        fderiv Real F (controlledBaseEndpoint Ψ t z)‖ ≤ η := by
    intro u hu
    exact hρsmall h hsmall (by simpa [idLin] using hzh0) t ht u hu
  have hTaylor :=
    flowTaylorRem_norm_le
      (F := F) (Φ := fun y τ => controlledBaseEndpoint Ψ τ y)
      (z := z) (h := h) (t := t)
      (s := s) (convex_segment _ _)
      (fun q _hq => hFdiff q)
      (left_mem_segment Real _ _)
      (right_mem_segment Real _ _)
      hD
  have hsep :=
    controlledBase_dist_le_of_lipschitz
      (x0 := x0) (Ψ := Ψ) (r := r) (L' := L') (z := z) (h := h)
      (t := t) (hLip t ht) (by simpa [idLin] using hz0)
      (by simpa [idLin] using hzh0)
  rw [dist_eq_norm] at hsep
  exact hTaylor.trans
    (mul_le_mul_of_nonneg_left hsep (le_of_lt hη))

/-- Controlled-ball variant of the Taylor-residual forcing estimate.  This is
the form needed for local vector fields: differentiability is only required on
the controlled ball that contains the relevant trajectory segments. -/
theorem controlledTaylorRem_eventually_of_lipschitz_on_ball
    {F : X -> X} {x0 z : X}
    {Ψ : X × (X →L[Real] X) -> Real -> X × (X →L[Real] X)}
    {a r L' : NNReal} {b : Real}
    (hbound :
      ∀ p ∈ Metric.closedBall (x0, ContinuousLinearMap.id Real X) r,
        ∀ t : Real,
          Ψ p t ∈ Metric.closedBall (x0, ContinuousLinearMap.id Real X) a)
    (hFdiff :
      ∀ q ∈ Metric.closedBall x0 (a : Real), DifferentiableAt Real F q)
    (hDcont :
      ∀ q ∈ Metric.closedBall x0 (a : Real),
        ContinuousAt (fderiv Real F) q)
    (hbase :
      ContinuousOn (fun t : Real => controlledBaseEndpoint Ψ t z)
        (Set.Icc (0 : Real) b))
    (hLip : ∀ t ∈ Set.Ico (0 : Real) b,
      LipschitzOnWith L'
        (fun p => Ψ p t)
        (Metric.closedBall (x0, ContinuousLinearMap.id Real X) r))
    (hzopen :
      (z, ContinuousLinearMap.id Real X) ∈
        Metric.ball (x0, ContinuousLinearMap.id Real X) r) :
    ∀ η > 0, ∀ᶠ h : X in 𝓝 0,
      ∀ t ∈ Set.Ico (0 : Real) b,
        ‖flowTaylorRem F (fun y τ => controlledBaseEndpoint Ψ τ y) z h t‖ ≤
          η * ((L' : Real) * ‖h‖) := by
  let idLin : X →L[Real] X := ContinuousLinearMap.id Real X
  have hz0 :
      (z, idLin) ∈ Metric.closedBall (x0, ContinuousLinearMap.id Real X) r := by
    exact Metric.ball_subset_closedBall (by simpa [idLin] using hzopen)
  have hbase_mem :
      ∀ t ∈ Set.Icc (0 : Real) b,
        controlledBaseEndpoint Ψ t z ∈ Metric.closedBall x0 (a : Real) := by
    intro t _ht
    have hp := hbound (z, idLin) (by simpa [idLin] using hz0) t
    rw [Metric.mem_closedBall] at hp ⊢
    rw [Prod.dist_eq] at hp
    exact (le_max_left _ _).trans hp
  have hDcont_img :
      ∀ y ∈ (fun t : Real => controlledBaseEndpoint Ψ t z) ''
          Set.Icc (0 : Real) b,
        ContinuousAt (fderiv Real F) y := by
    intro y hy
    rcases hy with ⟨t, ht, rfl⟩
    exact hDcont _ (hbase_mem t ht)
  have hDsmall :=
    controlled_fderiv_segment_small_of_lipschitz
      (F := F) (x0 := x0) (z := z) (Ψ := Ψ)
      (r := r) (L' := L') (b := b)
      hbase hDcont_img hLip (by simpa [idLin] using hz0)
  have hinit_cont :
      ContinuousAt (fun h : X => (z + h, idLin)) 0 := by
    have hleft : ContinuousAt (fun h : X => z + h) 0 := by
      simpa using (continuousAt_const.add continuousAt_id :
        ContinuousAt (fun h : X => z + h) 0)
    exact hleft.prodMk_nhds continuousAt_const
  have hzh_eventually :
      ∀ᶠ h : X in 𝓝 0,
        (z + h, idLin) ∈
          Metric.closedBall (x0, ContinuousLinearMap.id Real X) r := by
    have hzopen0 :
        (fun h : X => (z + h, idLin)) 0 ∈
            Metric.ball (x0, ContinuousLinearMap.id Real X) r := by
      simpa [idLin] using hzopen
    filter_upwards
      [hinit_cont.eventually (Metric.isOpen_ball.mem_nhds hzopen0)] with h hh
    exact Metric.ball_subset_closedBall hh
  intro η hη
  obtain ⟨ρ, hρ, hρsmall⟩ := hDsmall η hη
  have hmul_cont :
      Continuous (fun h : X => (L' : Real) * ‖h‖) :=
    continuous_const.mul continuous_norm
  have hsmall_eventually :
      ∀ᶠ h : X in 𝓝 0, (L' : Real) * ‖h‖ < ρ := by
    have hball :=
      (hmul_cont.continuousAt (x := (0 : X))).eventually
        (Metric.ball_mem_nhds ((L' : Real) * ‖(0 : X)‖) hρ)
    filter_upwards [hball] with h hh
    have habs : |(L' : Real) * ‖h‖| < ρ := by
      simpa [Real.dist_eq] using hh
    exact (abs_lt.1 habs).2
  filter_upwards [hzh_eventually, hsmall_eventually] with h hzh0 hsmall
  intro t ht
  have htcc : t ∈ Set.Icc (0 : Real) b :=
    Set.Ico_subset_Icc_self ht
  have hzh_mem :
      controlledBaseEndpoint Ψ t (z + h) ∈
        Metric.closedBall x0 (a : Real) := by
    have hp := hbound (z + h, idLin) (by simpa [idLin] using hzh0) t
    rw [Metric.mem_closedBall] at hp ⊢
    rw [Prod.dist_eq] at hp
    exact (le_max_left _ _).trans hp
  let s : Set X :=
    segment Real (controlledBaseEndpoint Ψ t z)
      (controlledBaseEndpoint Ψ t (z + h))
  have hseg_sub : s ⊆ Metric.closedBall x0 (a : Real) := by
    exact (convex_closedBall x0 (a : Real)).segment_subset
      (hbase_mem t htcc) hzh_mem
  have hD : ∀ u ∈ s,
      ‖fderiv Real F u -
        fderiv Real F (controlledBaseEndpoint Ψ t z)‖ ≤ η := by
    intro u hu
    exact hρsmall h hsmall (by simpa [idLin] using hzh0) t ht u hu
  have hTaylor :=
    flowTaylorRem_norm_le
      (F := F) (Φ := fun y τ => controlledBaseEndpoint Ψ τ y)
      (z := z) (h := h) (t := t)
      (s := s) (convex_segment _ _)
      (fun q hq => hFdiff q (hseg_sub hq))
      (left_mem_segment Real _ _)
      (right_mem_segment Real _ _)
      hD
  have hsep :=
    controlledBase_dist_le_of_lipschitz
      (x0 := x0) (Ψ := Ψ) (r := r) (L' := L') (z := z) (h := h)
      (t := t) (hLip t ht) (by simpa [idLin] using hz0)
      (by simpa [idLin] using hzh0)
  rw [dist_eq_norm] at hsep
  exact hTaylor.trans
    (mul_le_mul_of_nonneg_left hsep (le_of_lt hη))

theorem flowErrorRHS_eq_taylorRem_add
    (F : X -> X) (Φ : X -> Real -> X) (A : X -> Real -> X →L[Real] X)
    (z h : X) (t : Real) :
    flowErrorRHS F Φ A z h t =
      flowTaylorRem F Φ z h t +
        fderiv Real F (Φ z t) (flowError Φ A z h t) := by
  simp only [flowErrorRHS, flowTaylorRem, flowError]
  simp only [map_sub]
  abel

/-- Gronwall-ready pointwise estimate for the generic variational-error RHS. -/
theorem flowErrorRHS_norm_le
    (F : X -> X) (Φ : X -> Real -> X) (A : X -> Real -> X →L[Real] X)
    (z h : X) (t : Real) {B ε : Real}
    (hB : ‖fderiv Real F (Φ z t)‖ ≤ B)
    (hRem : ‖flowTaylorRem F Φ z h t‖ ≤ ε) :
    ‖flowErrorRHS F Φ A z h t‖ ≤ B * ‖flowError Φ A z h t‖ + ε := by
  let D := fderiv Real F (Φ z t)
  have hLin0 : ‖D (flowError Φ A z h t)‖ ≤ ‖D‖ * ‖flowError Φ A z h t‖ :=
    D.le_opNorm _
  have hLin : ‖D (flowError Φ A z h t)‖ ≤
      B * ‖flowError Φ A z h t‖ := by
    exact hLin0.trans
      (mul_le_mul_of_nonneg_right (by simpa [D] using hB) (norm_nonneg _))
  rw [flowErrorRHS_eq_taylorRem_add]
  calc
    ‖flowTaylorRem F Φ z h t + D (flowError Φ A z h t)‖
        ≤ ‖D (flowError Φ A z h t)‖ + ‖flowTaylorRem F Φ z h t‖ := by
          simpa [add_comm] using
            norm_add_le (flowTaylorRem F Φ z h t) (D (flowError Φ A z h t))
    _ ≤ B * ‖flowError Φ A z h t‖ + ε := add_le_add hLin hRem

/-- If the variational approximation error is little-o in the initial
perturbation, then the variational linear map is the Frechet derivative of the
fixed-time flow endpoint. -/
theorem flow_hasFDerivAt_of_error
    {Φ : X -> Real -> X} {A : X -> Real -> X →L[Real] X}
    {z : X} {t : Real}
    (herr : (fun h : X => flowError Φ A z h t) =o[𝓝 0] (fun h : X => h)) :
    HasFDerivAt (fun z' : X => Φ z' t) (A z t) z := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  simpa [flowError] using herr

/-- Fixed-time C1 dependence from an eventual Gronwall bound with a vanishing
Taylor-residual coefficient. -/
theorem flow_hasFDerivAt_of_gronwall
    {Φ : X -> Real -> X} {A : X -> Real -> X →L[Real] X}
    {z : X} {t B L T : Real} {C : X -> Real}
    (hC : Tendsto C (𝓝 0) (𝓝 0))
    (hbound : ∀ᶠ h in 𝓝 (0 : X),
      ‖flowError Φ A z h t‖ ≤ gronwallBound 0 B (C h * (L * ‖h‖)) T) :
    HasFDerivAt (fun z' : X => Φ z' t) (A z t) z := by
  apply flow_hasFDerivAt_of_error
  exact isLittleO_of_gronwall_bound
    (f := fun h : X => flowError Φ A z h t)
    (C := C) (B := B) (L := L) (T := T) hC hbound

/-- The variational approximation error is continuous on an interval if the
base flow and variational linear map are continuous there. -/
theorem flowError_continuousOn
    {Φ : X -> Real -> X} {A : X -> Real -> X →L[Real] X}
    {z h : X} {s : Set Real}
    (hzh : ContinuousOn (fun t => Φ (z + h) t) s)
    (hz : ContinuousOn (fun t => Φ z t) s)
    (hA : ContinuousOn (fun t => A z t) s) :
    ContinuousOn (flowError Φ A z h) s := by
  have happ : ContinuousOn (fun t => A z t h) s :=
    hA.clm_apply continuousOn_const
  simpa [flowError] using (hzh.sub hz).sub happ

/-- The model-independent variational error satisfies the expected
inhomogeneous linear ODE. -/
theorem flowError_hasDerivWithinAt
    {F : X -> X} {Φ : X -> Real -> X} {A : X -> Real -> X →L[Real] X}
    {z h : X} {s : Set Real} {t : Real}
    (hzh : HasDerivWithinAt (Φ (z + h)) (F (Φ (z + h) t)) s t)
    (hz : HasDerivWithinAt (Φ z) (F (Φ z t)) s t)
    (hA :
      HasDerivWithinAt (A z)
        ((fderiv Real F (Φ z t)).comp (A z t)) s t) :
    HasDerivWithinAt
      (flowError Φ A z h)
      (flowErrorRHS F Φ A z h t) s t := by
  have hh : HasDerivWithinAt (fun _ : Real => h) (0 : X) s t := by
    simpa using (hasDerivWithinAt_const (c := h) (s := s) (x := t))
  have hAh :
      HasDerivWithinAt (fun t : Real => A z t h)
        (((fderiv Real F (Φ z t)).comp (A z t)) h) s t := by
    simpa [ContinuousLinearMap.comp_apply] using hA.clm_apply hh
  have herr := (hzh.sub hz).sub hAh
  simpa [flowError, flowErrorRHS, ContinuousLinearMap.comp_apply] using herr

/-- The variational approximation error vanishes initially if the flow and
linearized flow have the expected initial values. -/
@[simp] theorem flowError_zero
    {Φ : X -> Real -> X} {A : X -> Real -> X →L[Real] X}
    {z h : X}
    (hzh : Φ (z + h) 0 = z + h)
    (hz : Φ z 0 = z)
    (hA : A z 0 = ContinuousLinearMap.id Real X) :
    flowError Φ A z h 0 = 0 := by
  simp [flowError, hzh, hz, hA]

/-- Generic Gronwall bound for the variational approximation error once the
error RHS has the standard linear-plus-forcing estimate. -/
theorem flowError_norm_le_gronwall
    (F : X -> X) (Φ : X -> Real -> X) (A : X -> Real -> X →L[Real] X)
    (z h : X) {a b δ K ε : Real}
    (hcont : ContinuousOn (flowError Φ A z h) (Set.Icc a b))
    (hderiv : ∀ t ∈ Set.Ico a b,
      HasDerivWithinAt (flowError Φ A z h)
        (flowErrorRHS F Φ A z h t) (Set.Ici t) t)
    (ha : ‖flowError Φ A z h a‖ ≤ δ)
    (hbound : ∀ t ∈ Set.Ico a b,
      ‖flowErrorRHS F Φ A z h t‖ ≤ K * ‖flowError Φ A z h t‖ + ε) :
    ∀ t ∈ Set.Icc a b,
      ‖flowError Φ A z h t‖ ≤ gronwallBound δ K ε (t - a) :=
  norm_le_gronwallBound_of_norm_deriv_right_le hcont hderiv ha hbound

/-- Generic fixed-time C1 dependence from the variational equation plus a
uniform Taylor-residual forcing estimate.

This is the reusable Gronwall theorem that the finite jet-prefix induction
should instantiate for each finite-dimensional jet RHS. -/
theorem flow_hasFDerivAt_of_taylor_gronwall
    {F : X -> X} {Φ : X -> Real -> X} {A : X -> Real -> X →L[Real] X}
    {z : X} {b B L : Real}
    (hb0 : 0 ≤ b)
    (hcont : ∀ᶠ h : X in 𝓝 0,
      ContinuousOn (flowError Φ A z h) (Set.Icc (0 : Real) b))
    (hderiv : ∀ᶠ h : X in 𝓝 0,
      ∀ t ∈ Set.Ico (0 : Real) b,
        HasDerivWithinAt (flowError Φ A z h)
          (flowErrorRHS F Φ A z h t) (Set.Ici t) t)
    (hzero : ∀ᶠ h : X in 𝓝 0, flowError Φ A z h 0 = 0)
    (hB : ∀ t ∈ Set.Ico (0 : Real) b,
      ‖fderiv Real F (Φ z t)‖ ≤ B)
    (hRem : ∀ η > 0, ∀ᶠ h : X in 𝓝 0,
      ∀ t ∈ Set.Ico (0 : Real) b,
        ‖flowTaylorRem F Φ z h t‖ ≤ η * (L * ‖h‖)) :
    HasFDerivAt (fun z' : X => Φ z' b) (A z b) z := by
  apply flow_hasFDerivAt_of_error
  refine
    isLittleO_of_gronwall_bound_eventually
      (X := X) (Y := X) (B := B) (L := L) (T := b) ?_
  intro η hη
  filter_upwards [hcont, hderiv, hzero, hRem η hη] with h hcont_h hderiv_h hzero_h hRem_h
  have hgr :
      ∀ t ∈ Set.Icc (0 : Real) b,
        ‖flowError Φ A z h t‖ ≤
          gronwallBound 0 B (η * (L * ‖h‖)) (t - 0) := by
    refine flowError_norm_le_gronwall F Φ A z h hcont_h hderiv_h ?_ ?_
    · simp [hzero_h]
    · intro t ht
      exact flowErrorRHS_norm_le F Φ A z h t (hB t ht) (hRem_h t ht)
  simpa using hgr b ⟨hb0, le_rfl⟩

/-- Generic controlled C1 dependence for an augmented variational flow, once
the uniform derivative bound and Taylor-residual estimate have been produced.

This theorem removes the model-spray and chart-source assumptions from the
Gronwall argument.  The remaining analytic inputs are exactly the estimates
needed by `flow_hasFDerivAt_of_taylor_gronwall`. -/
theorem controlledVarFlow_hasFDerivAt
    {F : X -> X}
    {x0 z : X}
    {Ψ : X × (X →L[Real] X) -> Real -> X × (X →L[Real] X)}
    {r : NNReal} {ε b B L : Real}
    (hb0 : 0 ≤ b)
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hflow :
      ∀ p ∈ Metric.closedBall (x0, ContinuousLinearMap.id Real X) r,
        Ψ p 0 = p ∧
          ∀ t ∈ Set.Icc (-ε) ε,
            HasDerivWithinAt (Ψ p)
              (variationalRHS F (Ψ p t)) (Set.Icc (-ε) ε) t)
    (hB : ∀ t ∈ Set.Ico (0 : Real) b,
      ‖fderiv Real F (controlledBaseEndpoint Ψ t z)‖ ≤ B)
    (hRem : ∀ η > 0, ∀ᶠ h : X in 𝓝 0,
      ∀ t ∈ Set.Ico (0 : Real) b,
        ‖flowTaylorRem F (fun y τ => controlledBaseEndpoint Ψ τ y) z h t‖ ≤
          η * (L * ‖h‖))
    (hzopen :
      (z, ContinuousLinearMap.id Real X) ∈
        Metric.ball (x0, ContinuousLinearMap.id Real X) r) :
    HasFDerivAt
      (fun z' : X => controlledBaseEndpoint Ψ b z')
      (controlledDerivEndpoint Ψ b z)
      z := by
  let idLin : X →L[Real] X := ContinuousLinearMap.id Real X
  let pz : X × (X →L[Real] X) := (z, idLin)
  have hz0 :
      pz ∈ Metric.closedBall (x0, ContinuousLinearMap.id Real X) r := by
    exact Metric.ball_subset_closedBall (by simpa [pz, idLin] using hzopen)
  have hinit_cont :
      ContinuousAt (fun h : X => (z + h, idLin)) 0 := by
    have hleft : ContinuousAt (fun h : X => z + h) 0 := by
      simpa using (continuousAt_const.add continuousAt_id :
        ContinuousAt (fun h : X => z + h) 0)
    exact hleft.prodMk_nhds continuousAt_const
  have hzh_eventually :
      ∀ᶠ h : X in 𝓝 0,
        (z + h, idLin) ∈
          Metric.closedBall (x0, ContinuousLinearMap.id Real X) r := by
    have hzopen0 :
        (fun h : X => (z + h, idLin)) 0 ∈
            Metric.ball (x0, ContinuousLinearMap.id Real X) r := by
      simpa [idLin] using hzopen
    filter_upwards
      [hinit_cont.eventually (Metric.isOpen_ball.mem_nhds hzopen0)] with h hh
    exact Metric.ball_subset_closedBall hh
  refine
    flow_hasFDerivAt_of_taylor_gronwall
      (F := F) (Φ := fun y τ => controlledBaseEndpoint Ψ τ y)
      (A := fun y τ => controlledDerivEndpoint Ψ τ y)
      (z := z) (b := b) (B := B) (L := L)
      hb0 ?_ ?_ ?_ hB hRem
  · filter_upwards [hzh_eventually] with h hzh0
    have hcont_zh :
        ContinuousOn (fun t : Real => controlledBaseEndpoint Ψ t (z + h))
          (Set.Icc (0 : Real) b) := by
      have hcont :
          ContinuousOn (Ψ (z + h, idLin)) (Set.Icc (-ε) ε) :=
        HasDerivWithinAt.continuousOn ((hflow (z + h, idLin) hzh0).2)
      simpa [controlledBaseEndpoint, idLin] using
        continuous_fst.comp_continuousOn (hcont.mono hb)
    have hcont_z :
        ContinuousOn (fun t : Real => controlledBaseEndpoint Ψ t z)
          (Set.Icc (0 : Real) b) := by
      have hcont :
          ContinuousOn (Ψ pz) (Set.Icc (-ε) ε) :=
        HasDerivWithinAt.continuousOn ((hflow pz hz0).2)
      simpa [controlledBaseEndpoint, pz, idLin] using
        continuous_fst.comp_continuousOn (hcont.mono hb)
    have hcont_A :
        ContinuousOn (fun t : Real => controlledDerivEndpoint Ψ t z)
          (Set.Icc (0 : Real) b) := by
      have hcont :
          ContinuousOn (Ψ pz) (Set.Icc (-ε) ε) :=
        HasDerivWithinAt.continuousOn ((hflow pz hz0).2)
      simpa [controlledDerivEndpoint, pz, idLin] using
        continuous_snd.comp_continuousOn (hcont.mono hb)
    exact flowError_continuousOn hcont_zh hcont_z hcont_A
  · filter_upwards [hzh_eventually] with h hzh0
    intro t ht
    have htIcc : t ∈ Set.Icc (0 : Real) b :=
      Set.Ico_subset_Icc_self ht
    have htbig : t ∈ Set.Icc (-ε) ε := hb htIcc
    have hbase_zh :
        HasDerivWithinAt
          (controlledBaseEndpoint Ψ · (z + h))
          (F (controlledBaseEndpoint Ψ t (z + h)))
          (Set.Icc (-ε) ε) t :=
      controlledBase_hasDerivWithinAt
        (F := F) (Ψ := Ψ) ((hflow (z + h, idLin) hzh0).2 t htbig)
    have hbase_z :
        HasDerivWithinAt
          (controlledBaseEndpoint Ψ · z)
          (F (controlledBaseEndpoint Ψ t z))
          (Set.Icc (-ε) ε) t :=
      controlledBase_hasDerivWithinAt
        (F := F) (Ψ := Ψ) ((hflow pz hz0).2 t htbig)
    have hA :
        HasDerivWithinAt
          (controlledDerivEndpoint Ψ · z)
          ((fderiv Real F (controlledBaseEndpoint Ψ t z)).comp
            (controlledDerivEndpoint Ψ t z))
          (Set.Icc (-ε) ε) t :=
      controlledDeriv_hasDerivWithinAt
        (F := F) (Ψ := Ψ) ((hflow pz hz0).2 t htbig)
    have herr :
        HasDerivWithinAt
          (flowError (fun y τ => controlledBaseEndpoint Ψ τ y)
            (fun y τ => controlledDerivEndpoint Ψ τ y) z h)
          (flowErrorRHS F (fun y τ => controlledBaseEndpoint Ψ τ y)
            (fun y τ => controlledDerivEndpoint Ψ τ y) z h t)
          (Set.Icc (-ε) ε) t :=
      flowError_hasDerivWithinAt
        (F := F) (Φ := fun y τ => controlledBaseEndpoint Ψ τ y)
        (A := fun y τ => controlledDerivEndpoint Ψ τ y) (z := z) (h := h)
        hbase_zh hbase_z hA
    exact
      (herr.mono hb).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ht)
  · filter_upwards [hzh_eventually] with h hzh0
    have hbase_zh :
        controlledBaseEndpoint Ψ 0 (z + h) = z + h := by
      simpa [controlledBaseEndpoint, idLin] using
        congrArg Prod.fst ((hflow (z + h, idLin) hzh0).1)
    have hbase_z : controlledBaseEndpoint Ψ 0 z = z := by
      simpa [controlledBaseEndpoint, pz, idLin] using
        congrArg Prod.fst ((hflow pz hz0).1)
    have hA0 :
        controlledDerivEndpoint Ψ 0 z = ContinuousLinearMap.id Real X := by
      simpa [controlledDerivEndpoint, pz, idLin] using
        congrArg Prod.snd ((hflow pz hz0).1)
    exact flowError_zero hbase_zh hbase_z hA0

/-- Generic controlled C1 dependence where the analytic estimates are produced
from continuity of `D F` along the compact base trajectory. -/
theorem controlledVarFlow_hasFDerivAt_of_fderiv_continuous
    {F : X -> X}
    {x0 z : X}
    {Ψ : X × (X →L[Real] X) -> Real -> X × (X →L[Real] X)}
    {r L' : NNReal} {ε b : Real}
    (hb0 : 0 ≤ b)
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hflow :
      ∀ p ∈ Metric.closedBall (x0, ContinuousLinearMap.id Real X) r,
        Ψ p 0 = p ∧
          ∀ t ∈ Set.Icc (-ε) ε,
            HasDerivWithinAt (Ψ p)
              (variationalRHS F (Ψ p t)) (Set.Icc (-ε) ε) t)
    (hLip :
      ∀ t ∈ Set.Icc (-ε) ε,
        LipschitzOnWith L'
          (fun p => Ψ p t)
          (Metric.closedBall (x0, ContinuousLinearMap.id Real X) r))
    (hFdiff : ∀ q : X, DifferentiableAt Real F q)
    (hDcont :
      ∀ y ∈ (fun t : Real => controlledBaseEndpoint Ψ t z) ''
          Set.Icc (0 : Real) b,
        ContinuousAt (fderiv Real F) y)
    (hzopen :
      (z, ContinuousLinearMap.id Real X) ∈
        Metric.ball (x0, ContinuousLinearMap.id Real X) r) :
    HasFDerivAt
      (fun z' : X => controlledBaseEndpoint Ψ b z')
      (controlledDerivEndpoint Ψ b z)
      z := by
  let idLin : X →L[Real] X := ContinuousLinearMap.id Real X
  let pz : X × (X →L[Real] X) := (z, idLin)
  have hz0 :
      pz ∈ Metric.closedBall (x0, ContinuousLinearMap.id Real X) r := by
    exact Metric.ball_subset_closedBall (by simpa [pz, idLin] using hzopen)
  have hbase :
      ContinuousOn (fun t : Real => controlledBaseEndpoint Ψ t z)
        (Set.Icc (0 : Real) b) := by
    have hcont :
        ContinuousOn (Ψ pz) (Set.Icc (-ε) ε) :=
      HasDerivWithinAt.continuousOn ((hflow pz hz0).2)
    simpa [controlledBaseEndpoint, pz, idLin] using
      continuous_fst.comp_continuousOn (hcont.mono hb)
  obtain ⟨B, hBcc⟩ :=
    fderiv_bound_on_base
      (F := F) (γ := fun t : Real => controlledBaseEndpoint Ψ t z)
      hbase hDcont
  have hRem :=
    controlledTaylorRem_eventually_of_lipschitz
      (F := F) (x0 := x0) (z := z) (Ψ := Ψ)
      (r := r) (L' := L') (b := b)
      hFdiff hbase hDcont
      (fun t ht => hLip t (hb (Set.Ico_subset_Icc_self ht)))
      hzopen
  exact
    controlledVarFlow_hasFDerivAt
      (F := F) (x0 := x0) (Ψ := Ψ)
      (r := r) (ε := ε) (b := b) (B := B) (L := (L' : Real))
      hb0 hb hflow
      (fun t ht => hBcc t (Set.Ico_subset_Icc_self ht))
      hRem hzopen

/-- Generic controlled C1 dependence from controlled-ball differentiability
and continuity of `D F`. -/
theorem controlledVarFlow_hasFDerivAt_of_fderiv_ball
    {F : X -> X}
    {x0 z : X}
    {Ψ : X × (X →L[Real] X) -> Real -> X × (X →L[Real] X)}
    {a r L' : NNReal} {ε b : Real}
    (hb0 : 0 ≤ b)
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hflow :
      ∀ p ∈ Metric.closedBall (x0, ContinuousLinearMap.id Real X) r,
        Ψ p 0 = p ∧
          ∀ t ∈ Set.Icc (-ε) ε,
            HasDerivWithinAt (Ψ p)
              (variationalRHS F (Ψ p t)) (Set.Icc (-ε) ε) t)
    (hbound :
      ∀ p ∈ Metric.closedBall (x0, ContinuousLinearMap.id Real X) r,
        ∀ t : Real,
          Ψ p t ∈ Metric.closedBall (x0, ContinuousLinearMap.id Real X) a)
    (hLip :
      ∀ t ∈ Set.Icc (-ε) ε,
        LipschitzOnWith L'
          (fun p => Ψ p t)
          (Metric.closedBall (x0, ContinuousLinearMap.id Real X) r))
    (hFdiff :
      ∀ q ∈ Metric.closedBall x0 (a : Real), DifferentiableAt Real F q)
    (hDcont :
      ∀ q ∈ Metric.closedBall x0 (a : Real),
        ContinuousAt (fderiv Real F) q)
    (hzopen :
      (z, ContinuousLinearMap.id Real X) ∈
        Metric.ball (x0, ContinuousLinearMap.id Real X) r) :
    HasFDerivAt
      (fun z' : X => controlledBaseEndpoint Ψ b z')
      (controlledDerivEndpoint Ψ b z)
      z := by
  let idLin : X →L[Real] X := ContinuousLinearMap.id Real X
  let pz : X × (X →L[Real] X) := (z, idLin)
  have hz0 :
      pz ∈ Metric.closedBall (x0, ContinuousLinearMap.id Real X) r := by
    exact Metric.ball_subset_closedBall (by simpa [pz, idLin] using hzopen)
  have hbase :
      ContinuousOn (fun t : Real => controlledBaseEndpoint Ψ t z)
        (Set.Icc (0 : Real) b) := by
    have hcont :
        ContinuousOn (Ψ pz) (Set.Icc (-ε) ε) :=
      HasDerivWithinAt.continuousOn ((hflow pz hz0).2)
    simpa [controlledBaseEndpoint, pz, idLin] using
      continuous_fst.comp_continuousOn (hcont.mono hb)
  have hbase_mem :
      ∀ t ∈ Set.Icc (0 : Real) b,
        controlledBaseEndpoint Ψ t z ∈ Metric.closedBall x0 (a : Real) := by
    intro t _ht
    have hp := hbound pz hz0 t
    rw [Metric.mem_closedBall] at hp ⊢
    rw [Prod.dist_eq] at hp
    exact (le_max_left _ _).trans hp
  have hDcont_img :
      ∀ y ∈ (fun t : Real => controlledBaseEndpoint Ψ t z) ''
          Set.Icc (0 : Real) b,
        ContinuousAt (fderiv Real F) y := by
    intro y hy
    rcases hy with ⟨t, ht, rfl⟩
    exact hDcont _ (hbase_mem t ht)
  obtain ⟨B, hBcc⟩ :=
    fderiv_bound_on_base
      (F := F) (γ := fun t : Real => controlledBaseEndpoint Ψ t z)
      hbase hDcont_img
  have hRem :=
    controlledTaylorRem_eventually_of_lipschitz_on_ball
      (F := F) (x0 := x0) (z := z) (Ψ := Ψ)
      (a := a) (r := r) (L' := L') (b := b)
      hbound hFdiff hDcont hbase
      (fun t ht => hLip t (hb (Set.Ico_subset_Icc_self ht)))
      hzopen
  exact
    controlledVarFlow_hasFDerivAt
      (F := F) (x0 := x0) (Ψ := Ψ)
      (r := r) (ε := ε) (b := b) (B := B) (L := (L' : Real))
      hb0 hb hflow
      (fun t ht => hBcc t (Set.Ico_subset_Icc_self ht))
      hRem hzopen

/-- Generic `C1` fixed-time dependence for a controlled augmented variational
flow, assuming the Taylor-residual estimates are available uniformly on a
neighborhood. -/
theorem controlledBaseEndpoint_contDiffAt_one
    {F : X -> X}
    {x0 z : X}
    {Ψ : X × (X →L[Real] X) -> Real -> X × (X →L[Real] X)}
    {r L' : NNReal} {ε b B L : Real}
    (hb0 : 0 ≤ b)
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hflow :
      ∀ p ∈ Metric.closedBall (x0, ContinuousLinearMap.id Real X) r,
        Ψ p 0 = p ∧
          ∀ t ∈ Set.Icc (-ε) ε,
            HasDerivWithinAt (Ψ p)
              (variationalRHS F (Ψ p t)) (Set.Icc (-ε) ε) t)
    (hLip :
      ∀ t ∈ Set.Icc (-ε) ε,
        LipschitzOnWith L'
          (fun p => Ψ p t)
          (Metric.closedBall (x0, ContinuousLinearMap.id Real X) r))
    (hB : ∀ y : X,
      (y, ContinuousLinearMap.id Real X) ∈
        Metric.ball (x0, ContinuousLinearMap.id Real X) r ->
      ∀ t ∈ Set.Ico (0 : Real) b,
        ‖fderiv Real F (controlledBaseEndpoint Ψ t y)‖ ≤ B)
    (hRem : ∀ y : X,
      (y, ContinuousLinearMap.id Real X) ∈
        Metric.ball (x0, ContinuousLinearMap.id Real X) r ->
      ∀ η > 0, ∀ᶠ h : X in 𝓝 0,
        ∀ t ∈ Set.Ico (0 : Real) b,
          ‖flowTaylorRem F (fun y τ => controlledBaseEndpoint Ψ τ y)
              y h t‖ ≤ η * (L * ‖h‖))
    (hzopen :
      (z, ContinuousLinearMap.id Real X) ∈
        Metric.ball (x0, ContinuousLinearMap.id Real X) r) :
    ContDiffAt Real 1
      (fun z' : X => controlledBaseEndpoint Ψ b z') z := by
  let idLin : X →L[Real] X := ContinuousLinearMap.id Real X
  let U : Set X := {y | (y, idLin) ∈ Metric.ball (x0, idLin) r}
  have hpairCont :
      ContinuousAt (fun y : X => (y, idLin)) z :=
    ContinuousAt.prodMk continuousAt_id continuousAt_const
  have hU : U ∈ 𝓝 z :=
    hpairCont.preimage_mem_nhds
      (Metric.isOpen_ball.mem_nhds (by simpa [idLin] using hzopen))
  rw [contDiffAt_one_iff]
  refine
    ⟨fun y : X => controlledDerivEndpoint Ψ b y, U, hU, ?_, ?_⟩
  · have hbmem : b ∈ Set.Icc (-ε) ε := hb ⟨hb0, le_rfl⟩
    have hΨcontOn :
        ContinuousOn
          (fun p : X × (X →L[Real] X) => Ψ p b)
          (Metric.closedBall (x0, idLin) r) :=
      (hLip b hbmem).continuousOn
    have hpairContOn :
        ContinuousOn (fun y : X => (y, idLin)) U :=
      ContinuousOn.prodMk continuousOn_id continuousOn_const
    have hmaps :
        Set.MapsTo (fun y : X => (y, idLin)) U
          (Metric.closedBall (x0, idLin) r) := by
      intro y hy
      exact Metric.ball_subset_closedBall hy
    have hcomp :
        ContinuousOn (fun y : X => Ψ (y, idLin) b) U :=
      hΨcontOn.comp hpairContOn hmaps
    simpa [controlledDerivEndpoint, idLin] using hcomp.snd
  · intro y hy
    exact controlledVarFlow_hasFDerivAt
      (F := F) (x0 := x0) (Ψ := Ψ)
      (r := r) (ε := ε) (b := b) (B := B) (L := L)
      hb0 hb hflow (hB y (by simpa [U, idLin] using hy))
      (hRem y (by simpa [U, idLin] using hy))
      (by simpa [U, idLin] using hy)

/-- Generic `C1` fixed-time dependence from continuity of `D F` along all
nearby compact base trajectories. -/
theorem controlledBaseEndpoint_contDiffAt_one_of_fderiv_continuous
    {F : X -> X}
    {x0 z : X}
    {Ψ : X × (X →L[Real] X) -> Real -> X × (X →L[Real] X)}
    {r L' : NNReal} {ε b : Real}
    (hb0 : 0 ≤ b)
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hflow :
      ∀ p ∈ Metric.closedBall (x0, ContinuousLinearMap.id Real X) r,
        Ψ p 0 = p ∧
          ∀ t ∈ Set.Icc (-ε) ε,
            HasDerivWithinAt (Ψ p)
              (variationalRHS F (Ψ p t)) (Set.Icc (-ε) ε) t)
    (hLip :
      ∀ t ∈ Set.Icc (-ε) ε,
        LipschitzOnWith L'
          (fun p => Ψ p t)
          (Metric.closedBall (x0, ContinuousLinearMap.id Real X) r))
    (hFdiff : ∀ q : X, DifferentiableAt Real F q)
    (hDcont : ∀ y : X,
      (y, ContinuousLinearMap.id Real X) ∈
        Metric.ball (x0, ContinuousLinearMap.id Real X) r ->
      ∀ q ∈ (fun t : Real => controlledBaseEndpoint Ψ t y) ''
          Set.Icc (0 : Real) b,
        ContinuousAt (fderiv Real F) q)
    (hzopen :
      (z, ContinuousLinearMap.id Real X) ∈
        Metric.ball (x0, ContinuousLinearMap.id Real X) r) :
    ContDiffAt Real 1
      (fun z' : X => controlledBaseEndpoint Ψ b z') z := by
  let idLin : X →L[Real] X := ContinuousLinearMap.id Real X
  let U : Set X := {y | (y, idLin) ∈ Metric.ball (x0, idLin) r}
  have hpairCont :
      ContinuousAt (fun y : X => (y, idLin)) z :=
    ContinuousAt.prodMk continuousAt_id continuousAt_const
  have hU : U ∈ 𝓝 z :=
    hpairCont.preimage_mem_nhds
      (Metric.isOpen_ball.mem_nhds (by simpa [idLin] using hzopen))
  rw [contDiffAt_one_iff]
  refine
    ⟨fun y : X => controlledDerivEndpoint Ψ b y, U, hU, ?_, ?_⟩
  · have hbmem : b ∈ Set.Icc (-ε) ε := hb ⟨hb0, le_rfl⟩
    have hΨcontOn :
        ContinuousOn
          (fun p : X × (X →L[Real] X) => Ψ p b)
          (Metric.closedBall (x0, idLin) r) :=
      (hLip b hbmem).continuousOn
    have hpairContOn :
        ContinuousOn (fun y : X => (y, idLin)) U :=
      ContinuousOn.prodMk continuousOn_id continuousOn_const
    have hmaps :
        Set.MapsTo (fun y : X => (y, idLin)) U
          (Metric.closedBall (x0, idLin) r) := by
      intro y hy
      exact Metric.ball_subset_closedBall hy
    have hcomp :
        ContinuousOn (fun y : X => Ψ (y, idLin) b) U :=
      hΨcontOn.comp hpairContOn hmaps
    simpa [controlledDerivEndpoint, idLin] using hcomp.snd
  · intro y hy
    exact controlledVarFlow_hasFDerivAt_of_fderiv_continuous
      (F := F) (x0 := x0) (Ψ := Ψ)
      (r := r) (L' := L') (ε := ε) (b := b)
      hb0 hb hflow hLip hFdiff
      (hDcont y (by simpa [U, idLin] using hy))
      (by simpa [U, idLin] using hy)

/-- Generic `C1` fixed-time dependence from controlled-ball differentiability
and continuity of `D F`, uniformly for nearby initial points. -/
theorem controlledBaseEndpoint_contDiffAt_one_of_fderiv_ball
    {F : X -> X}
    {x0 z : X}
    {Ψ : X × (X →L[Real] X) -> Real -> X × (X →L[Real] X)}
    {a r L' : NNReal} {ε b : Real}
    (hb0 : 0 ≤ b)
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hflow :
      ∀ p ∈ Metric.closedBall (x0, ContinuousLinearMap.id Real X) r,
        Ψ p 0 = p ∧
          ∀ t ∈ Set.Icc (-ε) ε,
            HasDerivWithinAt (Ψ p)
              (variationalRHS F (Ψ p t)) (Set.Icc (-ε) ε) t)
    (hbound :
      ∀ p ∈ Metric.closedBall (x0, ContinuousLinearMap.id Real X) r,
        ∀ t : Real,
          Ψ p t ∈ Metric.closedBall (x0, ContinuousLinearMap.id Real X) a)
    (hLip :
      ∀ t ∈ Set.Icc (-ε) ε,
        LipschitzOnWith L'
          (fun p => Ψ p t)
          (Metric.closedBall (x0, ContinuousLinearMap.id Real X) r))
    (hFdiff :
      ∀ q ∈ Metric.closedBall x0 (a : Real), DifferentiableAt Real F q)
    (hDcont :
      ∀ q ∈ Metric.closedBall x0 (a : Real),
        ContinuousAt (fderiv Real F) q)
    (hzopen :
      (z, ContinuousLinearMap.id Real X) ∈
        Metric.ball (x0, ContinuousLinearMap.id Real X) r) :
    ContDiffAt Real 1
      (fun z' : X => controlledBaseEndpoint Ψ b z') z := by
  let idLin : X →L[Real] X := ContinuousLinearMap.id Real X
  let U : Set X := {y | (y, idLin) ∈ Metric.ball (x0, idLin) r}
  have hpairCont :
      ContinuousAt (fun y : X => (y, idLin)) z :=
    ContinuousAt.prodMk continuousAt_id continuousAt_const
  have hU : U ∈ 𝓝 z :=
    hpairCont.preimage_mem_nhds
      (Metric.isOpen_ball.mem_nhds (by simpa [idLin] using hzopen))
  rw [contDiffAt_one_iff]
  refine
    ⟨fun y : X => controlledDerivEndpoint Ψ b y, U, hU, ?_, ?_⟩
  · have hbmem : b ∈ Set.Icc (-ε) ε := hb ⟨hb0, le_rfl⟩
    have hΨcontOn :
        ContinuousOn
          (fun p : X × (X →L[Real] X) => Ψ p b)
          (Metric.closedBall (x0, idLin) r) :=
      (hLip b hbmem).continuousOn
    have hpairContOn :
        ContinuousOn (fun y : X => (y, idLin)) U :=
      ContinuousOn.prodMk continuousOn_id continuousOn_const
    have hmaps :
        Set.MapsTo (fun y : X => (y, idLin)) U
          (Metric.closedBall (x0, idLin) r) := by
      intro y hy
      exact Metric.ball_subset_closedBall hy
    have hcomp :
        ContinuousOn (fun y : X => Ψ (y, idLin) b) U :=
      hΨcontOn.comp hpairContOn hmaps
    simpa [controlledDerivEndpoint, idLin] using hcomp.snd
  · intro y hy
    exact controlledVarFlow_hasFDerivAt_of_fderiv_ball
      (F := F) (x0 := x0) (Ψ := Ψ)
      (a := a) (r := r) (L' := L') (ε := ε) (b := b)
      hb0 hb hflow hbound hLip hFdiff hDcont
      (by simpa [U, idLin] using hy)

end GenericC1Flow

end Coordinates
end RicciFlower
