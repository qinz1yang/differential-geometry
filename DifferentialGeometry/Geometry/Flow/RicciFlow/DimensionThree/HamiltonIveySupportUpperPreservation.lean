import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIveySupportUpper
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RicciPreservation

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

theorem hamiltonIveySupportCoefficient_continuousOn
    {K a t0 T : Real} (hK : 0 < K) (ha : 0 < a) (ht0 : t0 ≤ 0) :
    ContinuousOn (fun t : Real => hamiltonIveySupportCoefficient K a t0 t) (Set.Icc 0 T) := by
  unfold hamiltonIveySupportCoefficient
  have hden : ∀ t ∈ Set.Icc 0 T, 0 < 1 + 2 * K * (t - t0) := by
    intro t ht
    have ht0' : 0 ≤ t - t0 := by linarith [ht.1, ht0]
    nlinarith [mul_nonneg (mul_pos (by norm_num : (0 : ℝ) < 2) hK).le ht0']
  have hnum : ContinuousOn (fun t : Real => K * Real.exp (a + 2)) (Set.Icc 0 T) := by
    fun_prop
  have hdenc : ContinuousOn (fun t : Real => a * (1 + 2 * K * (t - t0))) (Set.Icc 0 T) := by
    fun_prop
  exact hnum.div hdenc (fun t ht => by
    have h1 : 0 < a * (1 + 2 * K * (t - t0)) := mul_pos ha (hden t ht)
    exact ne_of_gt h1)

theorem hamiltonIveySupportCoefficient_continuous_subtype
    {K a t0 T : Real} (hK : 0 < K) (ha : 0 < a) (ht0 : t0 ≤ 0) :
    Continuous (fun q : {t : Real // t ∈ Set.Icc 0 T} × M =>
      hamiltonIveySupportCoefficient K a t0 q.1.1) := by
  have hc : ContinuousOn (fun t : Real => hamiltonIveySupportCoefficient K a t0 t)
      (Set.Icc 0 T) :=
    hamiltonIveySupportCoefficient_continuousOn hK ha ht0
  have hc' : Continuous (fun t : {t : Real // t ∈ Set.Icc 0 T} =>
      hamiltonIveySupportCoefficient K a t0 (t : Real)) :=
    continuousOn_iff_continuous_restrict.mp hc
  exact hc'.comp continuous_fst

theorem hamiltonIveySupportUpperSecFamilyContinuousOnSet
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {K a t0 T : Real} (hK : 0 < K) (ha : 0 < a) (ht0 : t0 ≤ 0)
    (hTsub : Set.Icc 0 T ⊆ D.carrier) :
    Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 (Set.Icc 0 T)
      (fun t x => (hamiltonIveySupportUpperSec S K a t0) t x) := by
  have hcoef :
      Continuous (fun q : {t : Real // t ∈ Set.Icc 0 T} × M =>
        hamiltonIveySupportCoefficient K a t0 q.1.1) :=
    hamiltonIveySupportCoefficient_continuous_subtype hK ha ht0
  have hmetric :
      Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 (Set.Icc 0 T)
        (fun t x => metricTensorField (I := I) (S.base.metric t) x) := by
    have hcont := hS.smoothMetric.metricTensor_cont
    exact Tensor0SFamilyContinuousOnSet.mono (I := I) (M := M)
      (by simpa [SolutionOn.family] using hcont) hTsub
  have hscaled :
      Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 (Set.Icc 0 T)
        (fun t x => hamiltonIveySupportCoefficient K a t0 t •
          metricTensorField (I := I) (S.base.metric t) x) :=
    Tensor0SFamilyContinuousOnSet.smul (I := I) (M := M)
      (s := 2) (K := Set.Icc 0 T)
      (f := fun t x => hamiltonIveySupportCoefficient K a t0 t)
      (A := fun t x => metricTensorField (I := I) (S.base.metric t) x)
      hcoef hmetric
  have hpinch := pinchSecFamilyContinuousOnSet (I := I) (M := M) S hS
    ((1 + a) / (2 * a))
  have hpinch' := Tensor0SFamilyContinuousOnSet.mono (I := I) (M := M) hpinch hTsub
  have hneg := Tensor0SFamilyContinuousOnSet.const_smul (I := I) (M := M)
    (s := 2) (K := Set.Icc 0 T)
    (A := fun t x => (pinchSec (I := I) S ((1 + a) / (2 * a))) t x) (-1 : Real) hpinch'
  have hsub := Tensor0SFamilyContinuousOnSet.add (I := I) (M := M)
    (s := 2) (K := Set.Icc 0 T)
    (A := fun t x => hamiltonIveySupportCoefficient K a t0 t •
      metricTensorField (I := I) (S.base.metric t) x)
    (B := fun t x => (-1 : Real) • (pinchSec (I := I) S ((1 + a) / (2 * a))) t x)
    hscaled hneg
  simpa [hamiltonIveySupportUpperSec, hamiltonIveySupportPinchDelta, sub_eq_add_neg]
    using hsub

theorem hamiltonIveySupportUpperSec_tangentBundle_cont
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval} {K : Set Real}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {Kc a t0 T : Real} (hK : 0 < Kc) (ha : 0 < a) (ht0 : t0 ≤ 0)
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hKsub : K ⊆ Set.Icc 0 T) :
    Continuous (fun q : {t : Real // t ∈ K} × TangentBundle I M =>
      TotalSpace.mk' (Tensor0SModel 2 Real E)
        (E := fun x : M => Tensor0SSpace 2 I x) q.2.proj
        ((hamiltonIveySupportUpperSec S Kc a t0) q.1.1 q.2.proj)) := by
  exact Tensor0SFamilyContinuousOnSet.tangentBundle (I := I) (M := M)
    (Tensor0SFamilyContinuousOnSet.mono (I := I) (M := M)
      (hamiltonIveySupportUpperSecFamilyContinuousOnSet (I := I) S hS hK ha ht0 hTsub)
      hKsub)

theorem hamiltonIveySupportUpperSpatialModel
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (Kc a t0 : Real) :
    TensorSpatialDerivs (I := I) (M := M)
      (fun t : Real => S.base.connection t)
      (hamiltonIveySupportUpperSec S Kc a t0)
      (hamiltonIveySupportUpperNablaModel S a)
      (hamiltonIveySupportUpperNab2ModelSec S a) := by
  constructor
  · intro t
    letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2
    letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 3
    have hPinchFirst := (pinchSpatialModel (I := I) S ((1 + a) / (2 * a))).first t
    have hneg := TotalNabla0SRealizes.smul (I := I) (M := M) (-1 : Real) hPinchFirst
    have hmetric : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 2 (S.base.connection t)
        (hamiltonIveySupportCoefficient Kc a t0 t •
          metricTensorField (I := I) (S.base.metric t))
        (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) 3) := by
      have hz := zero_realizes_metric (I := I) (S.base.connection t)
        (S.base.metric t) (ricciMetricComp (I := I) S t)
      have hsmul := TotalNabla0SRealizes.smul (I := I) (M := M)
        (hamiltonIveySupportCoefficient Kc a t0 t) hz
      simpa using hsmul
    have hadd := TotalNabla0SRealizes.add (I := I) (M := M) hmetric hneg
    simpa [hamiltonIveySupportUpperSec, hamiltonIveySupportUpperNablaModel,
      hamiltonIveySupportPinchDelta, sub_eq_add_neg] using hadd
  · intro t
    letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 3
    letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 4
    have hPinchSecond := (pinchSpatialModel (I := I) S ((1 + a) / (2 * a))).second t
    have hneg := TotalNabla0SRealizes.smul (I := I) (M := M) (-1 : Real) hPinchSecond
    simpa [hamiltonIveySupportUpperNablaModel, hamiltonIveySupportUpperNab2ModelSec,
      hamiltonIveySupportPinchDelta] using hneg

theorem hamiltonIveySupportUpperReactAt_shiftCoeff_diff
    {K a t0 t c : Real} {g : SmoothRiemannianMetric I M} {x : M}
    {A : Tensor02At (I := I) (M := M) x}
    [SigmaCompactSpace M] [T2Space M]
    [IsManifold I 1 M]
    (ha : 0 < a)
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (v : TangentSpace I x) :
    hamiltonIveySupportUpperReactAt (I := I) K a t0 t g
        (A + c • metricTensorField (I := I) g x)
        (vec2 (I := I) v v) -
      hamiltonIveySupportUpperReactAt (I := I) K a t0 t g A
        (vec2 (I := I) v v) =
        c *
          (((2 * hamiltonIveySupportCoefficient K a t0 t /
              (1 - 3 * hamiltonIveySupportPinchDelta a)) : Real) *
              (g.inner x v v) +
            ((2 * hamiltonIveySupportPinchDelta a - 1) /
              (1 - 3 * hamiltonIveySupportPinchDelta a)) *
              (((3 : Real) • shiftRic3At (I := I) (M := M)
                  (hamiltonIveySupportPinchDelta a) g
                  (hamiltonIveySupportCoefficient K a t0 t •
                    metricTensorField (I := I) g x - A) -
                metricTracePair0SAt (I := I) g
                  (shiftRic3At (I := I) (M := M)
                    (hamiltonIveySupportPinchDelta a) g
                    (hamiltonIveySupportCoefficient K a t0 t •
                      metricTensorField (I := I) g x - A)) •
                  metricTensorField (I := I) g x)
                (vec2 (I := I) v v))) := by
  let ccoefL : Real := hamiltonIveySupportCoefficient K a t0 t
  let cderL : Real := hamiltonIveySupportCoefficientDeriv K a t0 t
  let deltaL : Real := hamiltonIveySupportPinchDelta a
  let QL : Tensor02At (I := I) (M := M) x :=
    ccoefL • metricTensorField (I := I) g x - A
  let RicL : Tensor02At (I := I) (M := M) x :=
    shiftRic3At (I := I) (M := M) deltaL g QL
  have hden0 : (1 : Real) - 3 * ((1 + a) / (2 * a)) ≠ 0 := by
    have hcalc : 1 - 3 * ((1 + a) / (2 * a)) = -(a + 3) / (2 * a) := by
      field_simp [ha.ne']
      ring
    rw [hcalc]
    have hnum : -(a + 3) ≠ 0 := by
      rw [neg_ne_zero]
      nlinarith
    exact div_ne_zero hnum (mul_ne_zero two_ne_zero ha.ne')
  have hden : (1 : Real) - 3 * deltaL ≠ 0 := by
    dsimp [deltaL]
    exact hden0
  obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt (I := I) g x hdim
  have hRicAdd := shiftRic_add_g (I := I) (M := M) (δ := deltaL) (c := -c)
    (g := g) (x := x) basis horth hden QL
  -- hRicAdd : shiftRic3At deltaL g (QL + -c • g) = shiftRic3At deltaL g QL + (-c / (1-3δ)) • g
  have hRicAdd' :
      shiftRic3At (I := I) (M := M) deltaL g
          (ccoefL • metricTensorField (I := I) g x - (A + c • metricTensorField (I := I) g x)) =
        shiftRic3At (I := I) (M := M) deltaL g QL +
          (-(c) / (1 - 3 * deltaL)) • metricTensorField (I := I) g x := by
    have hQ : ccoefL • metricTensorField (I := I) g x -
        (A + c • metricTensorField (I := I) g x) =
        QL + (-c) • metricTensorField (I := I) g x := by
      dsimp [QL]
      rw [neg_smul]
      abel
    rw [hQ]
    exact hRicAdd
  have hRicAdd'' :
      shiftRic3At (I := I) (M := M) (hamiltonIveySupportPinchDelta a) g
          (ccoefL • metricTensorField (I := I) g x -
            (A + c • metricTensorField (I := I) g x)) =
        shiftRic3At (I := I) (M := M) (hamiltonIveySupportPinchDelta a) g QL +
          (-(c) / (1 - 3 * hamiltonIveySupportPinchDelta a)) •
            metricTensorField (I := I) g x := by
    simpa [deltaL] using hRicAdd'
  have hNAt := shiftNAt_add_g_quad (I := I) (M := M)
    (delta := deltaL) (c := -c) (t := t) (g := g)
    (x := x) hden hdim QL v
  -- hNAt : shiftNAt deltaL t g x (QL + -c•g) (vec2 v v) - shiftNAt deltaL t g x QL (vec2 v v)
  --        = (-c / (1-3δ)) * (2δ - 1) * ((3•RicL - tr RicL • g) (vec2 v v))
  have hNAt' :
      shiftNAt (I := I) (M := M) deltaL t g x
          (ccoefL • metricTensorField (I := I) g x -
            (A + c • metricTensorField (I := I) g x))
          (vec2 (I := I) v v) -
        shiftNAt (I := I) (M := M) deltaL t g x QL
          (vec2 (I := I) v v) =
        (-c / (1 - 3 * deltaL)) * (2 * deltaL - 1) *
          ((3 : Real) • shiftRic3At (I := I) (M := M) deltaL g QL -
            metricTracePair0SAt (I := I) g
              (shiftRic3At (I := I) (M := M) deltaL g QL) •
              metricTensorField (I := I) g x)
            (vec2 (I := I) v v) := by
    have hQ : ccoefL • metricTensorField (I := I) g x -
        (A + c • metricTensorField (I := I) g x) =
        QL + (-c) • metricTensorField (I := I) g x := by
      dsimp [QL]
      rw [neg_smul]
      abel
    rw [hQ]
    exact hNAt
  have hNAt'' :
      shiftNAt (I := I) (M := M) (hamiltonIveySupportPinchDelta a) t g x
          (ccoefL • metricTensorField (I := I) g x -
            (A + c • metricTensorField (I := I) g x))
          (vec2 (I := I) v v) -
        shiftNAt (I := I) (M := M) (hamiltonIveySupportPinchDelta a) t g x
          (ccoefL • metricTensorField (I := I) g x - A)
          (vec2 (I := I) v v) =
        (-c / (1 - 3 * hamiltonIveySupportPinchDelta a)) *
          (2 * hamiltonIveySupportPinchDelta a - 1) *
          ((3 : Real) • shiftRic3At (I := I) (M := M)
              (hamiltonIveySupportPinchDelta a) g
              (ccoefL • metricTensorField (I := I) g x - A) -
            metricTracePair0SAt (I := I) g
              (shiftRic3At (I := I) (M := M)
                (hamiltonIveySupportPinchDelta a) g
                (ccoefL • metricTensorField (I := I) g x - A)) •
              metricTensorField (I := I) g x)
            (vec2 (I := I) v v) := by
    simpa [deltaL, QL] using hNAt'
  -- unfold the reaction at A + c•g and at A, and compute the difference
  change (hamiltonIveySupportCoefficientDeriv K a t0 t • metricTensorField (I := I) g x -
        (2 * hamiltonIveySupportCoefficient K a t0 t) •
          shiftRic3At (I := I) (M := M) (hamiltonIveySupportPinchDelta a) g
            (hamiltonIveySupportCoefficient K a t0 t • metricTensorField (I := I) g x -
              (A + c • metricTensorField (I := I) g x)) -
        shiftNAt (I := I) (M := M) (hamiltonIveySupportPinchDelta a) t g x
          (hamiltonIveySupportCoefficient K a t0 t • metricTensorField (I := I) g x -
            (A + c • metricTensorField (I := I) g x)))
        (vec2 (I := I) v v) -
      (hamiltonIveySupportCoefficientDeriv K a t0 t • metricTensorField (I := I) g x -
        (2 * hamiltonIveySupportCoefficient K a t0 t) •
          shiftRic3At (I := I) (M := M) (hamiltonIveySupportPinchDelta a) g
            (hamiltonIveySupportCoefficient K a t0 t • metricTensorField (I := I) g x - A) -
        shiftNAt (I := I) (M := M) (hamiltonIveySupportPinchDelta a) t g x
          (hamiltonIveySupportCoefficient K a t0 t • metricTensorField (I := I) g x - A))
        (vec2 (I := I) v v) =
    c *
      ((2 * hamiltonIveySupportCoefficient K a t0 t /
          (1 - 3 * hamiltonIveySupportPinchDelta a)) * ((g.inner x) v) v +
        ((2 * hamiltonIveySupportPinchDelta a - 1) /
          (1 - 3 * hamiltonIveySupportPinchDelta a)) *
          ((3 : Real) • shiftRic3At (I := I) (M := M)
              (hamiltonIveySupportPinchDelta a) g
              (hamiltonIveySupportCoefficient K a t0 t • metricTensorField (I := I) g x - A) -
            metricTracePair0SAt (I := I) g
              (shiftRic3At (I := I) (M := M) (hamiltonIveySupportPinchDelta a) g
                (hamiltonIveySupportCoefficient K a t0 t • metricTensorField (I := I) g x - A)) •
              metricTensorField (I := I) g x)
            (vec2 (I := I) v v))
  rw [hRicAdd'']
  dsimp [QL]
  let δ : Real := hamiltonIveySupportPinchDelta a
  let RicA : Tensor02At (I := I) (M := M) x :=
    shiftRic3At (I := I) (M := M) δ g (ccoefL • metricTensorField (I := I) g x - A)
  let XB : Tensor02At (I := I) (M := M) x :=
    shiftNAt (I := I) (M := M) δ t g x
      (ccoefL • metricTensorField (I := I) g x - (A + c • metricTensorField (I := I) g x))
  let YA : Tensor02At (I := I) (M := M) x :=
    shiftNAt (I := I) (M := M) δ t g x (ccoefL • metricTensorField (I := I) g x - A)
  change (cderL • metricTensorField (I := I) g x -
        (2 * ccoefL) • (RicA + (-(c) / (1 - 3 * δ)) • metricTensorField (I := I) g x) - XB)
        (vec2 (I := I) v v) -
      (cderL • metricTensorField (I := I) g x - (2 * ccoefL) • RicA - YA)
        (vec2 (I := I) v v) =
    c *
      ((2 * ccoefL / (1 - 3 * δ)) * ((g.inner x) v) v +
        ((2 * δ - 1) / (1 - 3 * δ)) *
          ((3 : Real) • RicA -
            metricTracePair0SAt (I := I) g RicA • metricTensorField (I := I) g x)
            (vec2 (I := I) v v))
  have hE1 : (cderL • metricTensorField (I := I) g x -
        (2 * ccoefL) • (RicA + (-(c) / (1 - 3 * δ)) • metricTensorField (I := I) g x) - XB)
        (vec2 (I := I) v v) =
      (cderL • metricTensorField (I := I) g x -
        (2 * ccoefL) • (RicA + (-(c) / (1 - 3 * δ)) • metricTensorField (I := I) g x))
          (vec2 (I := I) v v) - XB (vec2 (I := I) v v) :=
    Tensor0SSpace.sub_apply 2 x _ _ (vec2 (I := I) v v)
  rw [hE1]
  have hE2 : (cderL • metricTensorField (I := I) g x - (2 * ccoefL) • RicA - YA)
        (vec2 (I := I) v v) =
      (cderL • metricTensorField (I := I) g x - (2 * ccoefL) • RicA)
          (vec2 (I := I) v v) - YA (vec2 (I := I) v v) :=
    Tensor0SSpace.sub_apply 2 x _ _ (vec2 (I := I) v v)
  rw [hE2]
  have hE1' : (cderL • metricTensorField (I := I) g x -
        (2 * ccoefL) • (RicA + (-(c) / (1 - 3 * δ)) • metricTensorField (I := I) g x))
        (vec2 (I := I) v v) =
      (cderL • metricTensorField (I := I) g x) (vec2 (I := I) v v) -
        ((2 * ccoefL) • (RicA + (-(c) / (1 - 3 * δ)) • metricTensorField (I := I) g x))
          (vec2 (I := I) v v) :=
    Tensor0SSpace.sub_apply 2 x _ _ (vec2 (I := I) v v)
  rw [hE1']
  have hE2' : (cderL • metricTensorField (I := I) g x - (2 * ccoefL) • RicA)
        (vec2 (I := I) v v) =
      (cderL • metricTensorField (I := I) g x) (vec2 (I := I) v v) -
        ((2 * ccoefL) • RicA) (vec2 (I := I) v v) :=
    Tensor0SSpace.sub_apply 2 x _ _ (vec2 (I := I) v v)
  rw [hE2']
  have hSmul1 : ((2 * ccoefL) •
        (RicA + (-(c) / (1 - 3 * δ)) • metricTensorField (I := I) g x))
        (vec2 (I := I) v v) =
      (2 * ccoefL) *
        (RicA + (-(c) / (1 - 3 * δ)) • metricTensorField (I := I) g x)
          (vec2 (I := I) v v) :=
    Tensor0SSpace.smul_apply 2 x _ _ (vec2 (I := I) v v)
  rw [hSmul1]
  have hAdd : (RicA + (-(c) / (1 - 3 * δ)) • metricTensorField (I := I) g x)
        (vec2 (I := I) v v) =
      RicA (vec2 (I := I) v v) +
        ((-(c) / (1 - 3 * δ)) • metricTensorField (I := I) g x) (vec2 (I := I) v v) :=
    Tensor0SSpace.add_apply 2 x _ _ (vec2 (I := I) v v)
  rw [hAdd]
  have hSmul2 : ((2 * ccoefL) • RicA) (vec2 (I := I) v v) =
      (2 * ccoefL) * RicA (vec2 (I := I) v v) :=
    Tensor0SSpace.smul_apply 2 x _ _ (vec2 (I := I) v v)
  rw [hSmul2]
  have hSmul3 : (cderL • metricTensorField (I := I) g x) (vec2 (I := I) v v) =
      cderL * (metricTensorField (I := I) g x) (vec2 (I := I) v v) :=
    Tensor0SSpace.smul_apply 2 x _ _ (vec2 (I := I) v v)
  rw [hSmul3]
  have hSmul4 : ((-(c) / (1 - 3 * δ)) • metricTensorField (I := I) g x)
        (vec2 (I := I) v v) =
      (-(c) / (1 - 3 * δ)) * (metricTensorField (I := I) g x) (vec2 (I := I) v v) :=
    Tensor0SSpace.smul_apply 2 x _ _ (vec2 (I := I) v v)
  rw [hSmul4]
  have hMetric : (metricTensorField (I := I) g x) (vec2 (I := I) v v) =
      (g.inner x) (vec2 (I := I) v v 0) (vec2 (I := I) v v 1) := by
    simp [metricTensorField_apply]
  rw [hMetric]
  simp only [DifferentialGeometry.Geometry.Curvature.vec2, Fin.isValue, ↓reduceIte, one_ne_zero]
  let gvv : Real := (g.inner x) v v
  let Cvv : Real :=
    ((3 : Real) • RicA -
      metricTracePair0SAt (I := I) g RicA • metricTensorField (I := I) g x)
      (vec2 (I := I) v v)
  change cderL * gvv - 2 * ccoefL * (RicA (vec2 (I := I) v v) + (-c / (1 - 3 * δ)) * gvv) -
        XB (vec2 (I := I) v v) -
      (cderL * gvv - 2 * ccoefL * RicA (vec2 (I := I) v v) - YA (vec2 (I := I) v v)) =
    c * (2 * ccoefL / (1 - 3 * δ) * gvv + (2 * δ - 1) / (1 - 3 * δ) * Cvv)
  have hNAt4 : XB (vec2 (I := I) v v) - YA (vec2 (I := I) v v) =
      -c * ((2 * δ - 1) / (1 - 3 * δ)) * Cvv := by
    have hNAt''' : XB (vec2 (I := I) v v) - YA (vec2 (I := I) v v) =
        -c * ((2 * δ - 1) / (1 - 3 * δ)) *
          ((3 : Real) • RicA -
            metricTracePair0SAt (I := I) g RicA • metricTensorField (I := I) g x)
            (vec2 (I := I) v v) := by
      dsimp [δ, XB, YA, RicA]
      rw [hNAt'']
      ring
    simpa [Cvv] using hNAt'''
  have hmain : cderL * gvv - 2 * ccoefL * (RicA (vec2 (I := I) v v) + (-c / (1 - 3 * δ)) * gvv) -
        XB (vec2 (I := I) v v) -
      (cderL * gvv - 2 * ccoefL * RicA (vec2 (I := I) v v) - YA (vec2 (I := I) v v)) =
      c * (2 * ccoefL / (1 - 3 * δ) * gvv + (2 * δ - 1) / (1 - 3 * δ) * Cvv) := by
    calc
      cderL * gvv - 2 * ccoefL * (RicA (vec2 (I := I) v v) + (-c / (1 - 3 * δ)) * gvv) -
            XB (vec2 (I := I) v v) -
          (cderL * gvv - 2 * ccoefL * RicA (vec2 (I := I) v v) - YA (vec2 (I := I) v v))
          = cderL * gvv - 2 * ccoefL * (RicA (vec2 (I := I) v v) + (-c / (1 - 3 * δ)) * gvv) -
              XB (vec2 (I := I) v v) - cderL * gvv + 2 * ccoefL * RicA (vec2 (I := I) v v) +
              YA (vec2 (I := I) v v) := by ring
      _ = -2 * ccoefL * (-c / (1 - 3 * δ)) * gvv -
          (XB (vec2 (I := I) v v) - YA (vec2 (I := I) v v)) := by ring
      _ = 2 * ccoefL * c / (1 - 3 * δ) * gvv -
          (XB (vec2 (I := I) v v) - YA (vec2 (I := I) v v)) := by ring
      _ = 2 * ccoefL * c / (1 - 3 * δ) * gvv +
          c * ((2 * δ - 1) / (1 - 3 * δ)) * Cvv := by
        rw [hNAt4]
        ring
      _ = c * (2 * ccoefL / (1 - 3 * δ) * gvv + (2 * δ - 1) / (1 - 3 * δ) * Cvv) := by ring
  exact hmain

theorem hamiltonIveySupportUpperReact_barrier_diff
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    {K a epsilon d t0 tbar t : Real} {x : M}
    (ha : 0 < a)
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (v : TangentSpace I x) :
    (hamiltonIveySupportUpperReact (I := I) (M := M) K a t0 t (S.base.metric t)
        (tensorBarrierFamily (I := I) (M := M) (fun s : Real => S.base.metric s)
          (twoTensorSecToFamily (I := I) (M := M)
            (hamiltonIveySupportUpperSec S K a t0))
          epsilon d tbar t)) x v v -
      (hamiltonIveySupportUpperReact (I := I) (M := M) K a t0 t (S.base.metric t)
        (twoTensorSecToFamily (I := I) (M := M)
          (hamiltonIveySupportUpperSec S K a t0) t)) x v v =
        (epsilon * (d + t - tbar)) *
          (((2 * hamiltonIveySupportCoefficient K a t0 t /
              (1 - 3 * hamiltonIveySupportPinchDelta a)) : Real) *
              ((S.base.metric t).inner x v v) +
            ((2 * hamiltonIveySupportPinchDelta a - 1) /
              (1 - 3 * hamiltonIveySupportPinchDelta a)) *
              (((3 : Real) • shiftRic3At (I := I) (M := M)
                  (hamiltonIveySupportPinchDelta a) (S.base.metric t)
                  (hamiltonIveySupportCoefficient K a t0 t •
                      metricTensorField (I := I) (S.base.metric t) x -
                    (hamiltonIveySupportUpperSec S K a t0) t x) -
                metricTracePair0SAt (I := I) (S.base.metric t)
                  (shiftRic3At (I := I) (M := M)
                    (hamiltonIveySupportPinchDelta a) (S.base.metric t)
                    (hamiltonIveySupportCoefficient K a t0 t •
                        metricTensorField (I := I) (S.base.metric t) x -
                      (hamiltonIveySupportUpperSec S K a t0) t x)) •
                  metricTensorField (I := I) (S.base.metric t) x)
                (vec2 (I := I) v v))) := by
  let Araw : RawTwoTensorField (I := I) (M := M) :=
    twoTensorSecToFamily (I := I) (M := M)
      (hamiltonIveySupportUpperSec S K a t0) t
  let Barr : RawTwoTensorField (I := I) (M := M) :=
    tensorBarrierFamily (I := I) (M := M) (fun s : Real => S.base.metric s)
      (twoTensorSecToFamily (I := I) (M := M)
        (hamiltonIveySupportUpperSec S K a t0))
      epsilon d tbar t
  let c : Real := epsilon * (d + t - tbar)
  have hBarr : Barr = fun x v w => Araw x v w + c * (S.base.metric t).inner x v w := by
    funext x v w
    simp [Barr, Araw, c, tensorBarrierFamily_apply]
  have hbilinA : TwoTensorBilinearAt (I := I) (M := M) Araw x := by
    simpa [Araw] using
      twoTensorSecToFamily_bilin (I := I) (M := M)
        (hamiltonIveySupportUpperSec S K a t0) t x
  have hbilinB : TwoTensorBilinearAt (I := I) (M := M) Barr x := by
    simpa [Barr] using
      barrierBilinearAt (I := I) (M := M)
        (G := fun s : Real => S.base.metric s)
        (S := twoTensorSecToFamily (I := I) (M := M)
          (hamiltonIveySupportUpperSec S K a t0))
        (epsilon := epsilon) (delta := d) (t0 := tbar) (t := t) (x := x)
        (twoTensorSecToFamily_bilin (I := I) (M := M)
          (hamiltonIveySupportUpperSec S K a t0) t x)
  have hsymB : TwoTensorSymmetricAt (I := I) (M := M) Barr x := by
    exact barrierSymmAt (I := I) (M := M)
      (G := fun s : Real => S.base.metric s)
      (S := twoTensorSecToFamily (I := I) (M := M)
        (hamiltonIveySupportUpperSec S K a t0))
      (epsilon := epsilon) (delta := d) (t0 := tbar) (t := t) (x := x)
      ((hamiltonIveySupportUpperSec_symm (I := I) S K a t0 Set.univ)
        t (by simp) x)
  have hrealB :
      Tensor02RealizesRawAt (I := I) (M := M) (rawSym2 (I := I) (M := M) Barr) x
        ((hamiltonIveySupportUpperSec S K a t0) t x +
          c • metricTensorField (I := I) (S.base.metric t) x) := by
    intro X Y
    rw [rawSym2_eq_of_symm (I := I) (M := M) hsymB X Y]
    rw [hBarr]
    have hadd :
        ((hamiltonIveySupportUpperSec S K a t0) t x +
            c • metricTensorField (I := I) (S.base.metric t) x)
            (vec2 (I := I) X Y) =
          (hamiltonIveySupportUpperSec S K a t0) t x (vec2 (I := I) X Y) +
            (c • metricTensorField (I := I) (S.base.metric t) x) (vec2 (I := I) X Y) :=
      Tensor0SSpace.add_apply 2 x ((hamiltonIveySupportUpperSec S K a t0) t x)
        (c • metricTensorField (I := I) (S.base.metric t) x) (vec2 (I := I) X Y)
    rw [hadd]
    rw [show (c • metricTensorField (I := I) (S.base.metric t) x) (vec2 (I := I) X Y) =
          c * metricTensorField (I := I) (S.base.metric t) x (vec2 (I := I) X Y) from
        Tensor0SSpace.smul_apply 2 x c (metricTensorField (I := I) (S.base.metric t) x)
          (vec2 (I := I) X Y)]
    simp only [metricTensorField_apply]
    have h0 : vec2 (I := I) X Y 0 = X := by
      unfold DifferentialGeometry.Geometry.Curvature.vec2
      simp
    have h1 : vec2 (I := I) X Y 1 = Y := by
      unfold DifferentialGeometry.Geometry.Curvature.vec2
      norm_num
    rw [h0, h1]
    dsimp [Araw]
    rw [twoTensorSecToFamily_apply]
  have hrealBundled :
      Tensor02RealizesRawAt (I := I) (M := M) (rawSym2 (I := I) (M := M) Barr) x
        (tensor02OfRawAt (I := I) (M := M)
          (rawSym2 (I := I) (M := M) Barr) x
          (rawSym2_bilin (I := I) (M := M) hbilinB)) :=
    tensor02OfRawAt_realizes (I := I) (M := M)
      (rawSym2 (I := I) (M := M) Barr) x
      (rawSym2_bilin (I := I) (M := M) hbilinB)
  have hB : tensor02OfRawAt (I := I) (M := M)
        (rawSym2 (I := I) (M := M) Barr) x
        (rawSym2_bilin (I := I) (M := M) hbilinB) =
      (hamiltonIveySupportUpperSec S K a t0) t x +
        c • metricTensorField (I := I) (S.base.metric t) x :=
    tensor02_realizes_ext (I := I) (M := M) hrealBundled hrealB
  rw [hamiltonIveySupportUpperReact, Tensor02ReactionAt.toRawSymm_eval_of_bilin
    (I := I) (M := M) (fun _t g _x A => hamiltonIveySupportUpperReactAt (I := I) K a t0 _t g A)
    t (S.base.metric t) Barr x hbilinB]
  rw [hB]
  have hrealA :
      Tensor02RealizesRawAt (I := I) (M := M) (rawSym2 (I := I) (M := M) Araw) x
        ((hamiltonIveySupportUpperSec S K a t0) t x) := by
    intro X Y
    change (hamiltonIveySupportUpperSec S K a t0) t x (vec2 (I := I) X Y) =
      (rawSym2 (I := I) (M := M) Araw) x X Y
    rw [rawSym2_eq_of_symm (I := I) (M := M)
      ((hamiltonIveySupportUpperSec_symm (I := I) S K a t0 Set.univ) t (by simp) x) X Y]
    rw [twoTensorSecToFamily_apply]
  have hrealBundledA :
      Tensor02RealizesRawAt (I := I) (M := M) (rawSym2 (I := I) (M := M) Araw) x
        (tensor02OfRawAt (I := I) (M := M)
          (rawSym2 (I := I) (M := M) Araw) x
          (rawSym2_bilin (I := I) (M := M) hbilinA)) :=
    tensor02OfRawAt_realizes (I := I) (M := M)
      (rawSym2 (I := I) (M := M) Araw) x
      (rawSym2_bilin (I := I) (M := M) hbilinA)
  have hA : tensor02OfRawAt (I := I) (M := M)
        (rawSym2 (I := I) (M := M) Araw) x
        (rawSym2_bilin (I := I) (M := M) hbilinA) =
      (hamiltonIveySupportUpperSec S K a t0) t x :=
    tensor02_realizes_ext (I := I) (M := M) hrealBundledA hrealA
  rw [Tensor02ReactionAt.toRawSymm_eval_of_bilin
    (I := I) (M := M) (fun _t g _x A => hamiltonIveySupportUpperReactAt (I := I) K a t0 _t g A)
    t (S.base.metric t) Araw x hbilinA]
  rw [hA]
  rw [hamiltonIveySupportUpperReactAt_shiftCoeff_diff (I := I) (K := K) (a := a)
    (t0 := t0) (t := t) (c := c) (g := S.base.metric t) (x := x)
    (A := (hamiltonIveySupportUpperSec S K a t0) t x) ha hdim v]

theorem hamiltonIveySupportUpperReactLip_ltc_eq
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    {K a t0 t : Real} {x : M}
    (ha : 0 < a)
    (hdim : Module.finrank Real (TangentSpace I x) = 3) :
    (3 : Real) • shiftRic3At (I := I) (M := M) (hamiltonIveySupportPinchDelta a)
        (S.base.metric t)
        (hamiltonIveySupportCoefficient K a t0 t •
            metricTensorField (I := I) (S.base.metric t) x -
          (hamiltonIveySupportUpperSec S K a t0) t x) -
      metricTracePair0SAt (I := I) (S.base.metric t)
        (shiftRic3At (I := I) (M := M) (hamiltonIveySupportPinchDelta a)
          (S.base.metric t)
          (hamiltonIveySupportCoefficient K a t0 t •
              metricTensorField (I := I) (S.base.metric t) x -
            (hamiltonIveySupportUpperSec S K a t0) t x)) •
        metricTensorField (I := I) (S.base.metric t) x =
      metricTracePair0SAt (I := I) (S.base.metric t)
          ((hamiltonIveySupportUpperSec S K a t0) t x) •
          metricTensorField (I := I) (S.base.metric t) x -
        (3 : Real) • (hamiltonIveySupportUpperSec S K a t0) t x := by
  let g : SmoothRiemannianMetric I M := S.base.metric t
  let δ : Real := hamiltonIveySupportPinchDelta a
  let c : Real := hamiltonIveySupportCoefficient K a t0 t
  let Sx : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
    (hamiltonIveySupportUpperSec S K a t0) t x
  let Q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
    c • metricTensorField (I := I) g x - Sx
  letI : DistribSMul ℝ (Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :=
    (tensor0SSpace_module (𝕜 := ℝ) 2 x).toDistribMulAction.toDistribSMul
  letI : DistribMulAction ℝ (Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :=
    (tensor0SSpace_module (𝕜 := ℝ) 2 x).toDistribMulAction
  letI : MulAction ℝ (Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :=
    (tensor0SSpace_module (𝕜 := ℝ) 2 x).toDistribMulAction.toMulAction
  have hden0 : (1 : Real) - 3 * ((1 + a) / (2 * a)) ≠ 0 := by
    have hcalc : 1 - 3 * ((1 + a) / (2 * a)) = -(a + 3) / (2 * a) := by
      field_simp [ha.ne']
      ring
    rw [hcalc]
    have hnum : -(a + 3) ≠ 0 := by
      rw [neg_ne_zero]
      nlinarith
    exact div_ne_zero hnum (mul_ne_zero two_ne_zero ha.ne')
  have hden : (1 : Real) - 3 * δ ≠ 0 := by
    dsimp [δ]
    exact hden0
  obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt (I := I) g x hdim
  have hRic : shiftRic3At (I := I) (M := M) δ g Q =
      Q + (δ * metricTracePair0SAt (I := I) g Q / (1 - 3 * δ)) •
        metricTensorField (I := I) g x := by
    unfold shiftRic3At shiftScalar3At
    congr 1
    congr 1
    ring
  have htr : metricTracePair0SAt (I := I) g
        (Q + (δ * metricTracePair0SAt (I := I) g Q / (1 - 3 * δ)) •
          metricTensorField (I := I) g x) =
      metricTracePair0SAt (I := I) g Q +
        3 * (δ * metricTracePair0SAt (I := I) g Q / (1 - 3 * δ)) := by
    rw [metricTracePair0SAt_add (I := I) (M := M) g Q
      ((δ * metricTracePair0SAt (I := I) g Q / (1 - 3 * δ)) •
        metricTensorField (I := I) g x)]
    rw [metricTracePair0SAt_smul (I := I) (M := M) g
      (δ * metricTracePair0SAt (I := I) g Q / (1 - 3 * δ))
      (metricTensorField (I := I) g x)]
    rw [metricTrace_metric3 (I := I) (M := M) basis horth]
    ring
  have htrRic : metricTracePair0SAt (I := I) g (shiftRic3At (I := I) (M := M) δ g Q) =
      metricTracePair0SAt (I := I) g Q / (1 - 3 * δ) := by
    rw [hRic]
    rw [htr]
    field_simp [hden]
    ring
  -- C := 3•Ric - tr(Ric)•g = 3Q - tr(Q)•g = tr(S)•g - 3S
  have hQ : Q = c • metricTensorField (I := I) g x - Sx := rfl
  have htrQ : metricTracePair0SAt (I := I) g Q =
      3 * c - metricTracePair0SAt (I := I) g Sx := by
    rw [hQ]
    rw [metricTracePair0SAt_sub (I := I) (M := M) g
      (c • metricTensorField (I := I) g x) Sx]
    rw [metricTracePair0SAt_smul (I := I) (M := M) g c
      (metricTensorField (I := I) g x)]
    rw [metricTrace_metric3 (I := I) (M := M) basis horth]
    ring
  have hmain : (3 : Real) • shiftRic3At (I := I) (M := M) δ g Q -
      metricTracePair0SAt (I := I) g (shiftRic3At (I := I) (M := M) δ g Q) •
        metricTensorField (I := I) g x =
      metricTracePair0SAt (I := I) g Sx • metricTensorField (I := I) g x -
        (3 : Real) • Sx := by
    rw [hRic, htr]
    let s : Real := δ * metricTracePair0SAt (I := I) g Q / (1 - 3 * δ)
    have hsmul1 : (3 : Real) • (Q + s • metricTensorField (I := I) g x) =
        (3 : Real) • Q + (3 * s) • metricTensorField (I := I) g x := by
      calc
        (3 : Real) • (Q + s • metricTensorField (I := I) g x) =
            (3 : Real) • Q + (3 : Real) • (s • metricTensorField (I := I) g x) := by
          exact smul_add (3 : ℝ) Q (s • metricTensorField (I := I) g x)
        _ = (3 : Real) • Q + (3 * s) • metricTensorField (I := I) g x := by
          exact congrArg (fun T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x =>
            (3 : ℝ) • Q + T) (smul_smul (3 : ℝ) s (metricTensorField (I := I) g x))
    rw [hsmul1]
    have haddsmul : (metricTracePair0SAt (I := I) g Q + 3 * s) • metricTensorField (I := I) g x =
        metricTracePair0SAt (I := I) g Q • metricTensorField (I := I) g x +
          (3 * s) • metricTensorField (I := I) g x := by
      exact add_smul (metricTracePair0SAt (I := I) g Q) (3 * s) (metricTensorField (I := I) g x)
    dsimp [s]
    rw [haddsmul]
    dsimp [s]
    abel_nf
    rw [hQ, htrQ]
    have hsmul2 : (3 : Real) • (c • metricTensorField (I := I) g x - Sx) =
        (3 * c) • metricTensorField (I := I) g x - (3 : ℝ) • Sx := by
      have h1 := smul_sub (3 : ℝ) (c • metricTensorField (I := I) g x) Sx
      -- h1 : 3 • (c•g - S) = 3 • (c•g) - 3 • S
      simpa [smul_smul] using h1
    rw [hsmul2]
    have hsubsmul : (3 * c - metricTracePair0SAt (I := I) g Sx) • metricTensorField (I := I) g x =
        (3 * c) • metricTensorField (I := I) g x -
          metricTracePair0SAt (I := I) g Sx • metricTensorField (I := I) g x := by
      exact sub_smul (3 * c) (metricTracePair0SAt (I := I) g Sx) (metricTensorField (I := I) g x)
    rw [hsubsmul]
    abel_nf
  exact hmain

theorem hamiltonIveySupportUpperSec_absBound_Icc
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {K a t0 T : Real} (hK : 0 < K) (ha : 0 < a) (ht0 : t0 ≤ 0)
    {tstart t1 : Real}
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hsub : Set.Icc tstart t1 ⊆ Set.Icc 0 T) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ t, t ∈ Set.Icc tstart t1 -> ∀ x (v : TangentSpace I x),
        |quad02 (I := I) (M := M)
          ((hamiltonIveySupportUpperSec S K a t0) t x) v| ≤
          C * (S.base.metric t).inner x v v := by
  let G : Real -> SmoothRiemannianMetric I M := fun t => S.base.metric t
  let A : (t : Real) -> (x : M) -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 x :=
    fun t x => (hamiltonIveySupportUpperSec S K a t0) t x
  have hsubD : Set.Icc tstart t1 ⊆ D.carrier := by
    intro t ht
    exact hTsub (hsub ht)
  have hGcont :
      Continuous (metricTimeBundleQuad (I := I) (M := M) G (Set.Icc tstart t1)) := by
    simpa [G, SolutionOn.family] using
      metricTimeBundleQuad_cont_of_metricFamilySmoothOn (I := I) (M := M)
        S.family.metric hS.smoothMetric hsubD
  have hcompact :
      IsCompact
        (Set.univ :
          Set (MetricUnitTangentTimeSlab (I := I) (M := M) G
            (Set.Icc tstart t1))) :=
    metricUnitTimeSlab_icc_compact_of_bundle (I := I) (M := M)
      G tstart t1 (S.base.metric tstart) hGcont
  have hcont :
      Continuous
        (fun p : MetricUnitTangentTimeSlab (I := I) (M := M) G
            (Set.Icc tstart t1) =>
          |quad02 (I := I) (M := M)
            (A (MetricUnitTangentTimeSlab.time (I := I) (M := M) p)
              (MetricUnitTangentTimeSlab.base (I := I) (M := M) p))
            (MetricUnitTangentTimeSlab.vec (I := I) (M := M) p)|) :=
    timeSlabAbsQuadCont (I := I) (M := M) G A (Set.Icc tstart t1)
      (hamiltonIveySupportUpperSec_tangentBundle_cont (I := I) S hS hK ha ht0 hTsub hsub)
  obtain ⟨C, hC, hbound⟩ :=
    compactUnitTimeSlab_absBound (I := I) (M := M) G A (Set.Icc tstart t1) hcompact hcont
  refine ⟨C, hC, ?_⟩
  intro t ht x v
  simpa [G, A, quad02] using hbound t ht x v

theorem hamiltonIveySupportUpperSec_trace_abs_le
    {C : Real} (g : SmoothRiemannianMetric I M) {x : M}
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (hA : ∀ v : TangentSpace I x,
      |quad02 (I := I) (M := M) A v| ≤ C * g.inner x v v) :
    |metricTracePair0SAt (I := I) g A| ≤ 3 * C := by
  obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt (I := I) g x hdim
  have htr : metricTracePair0SAt (I := I) g A =
      ∑ i : Fin 3, A (vec2 (I := I) (basis i) (basis i)) := by
    rw [metricTracePair0SAt_eq_sum_basis (I := I) g basis
      DifferentialGeometry.Geometry.Curvature.delta3
      (orthonormal_invBasis3 (I := I) g basis horth) A]
    simp [DifferentialGeometry.Geometry.Curvature.delta3]
  rw [htr]
  have hAbsSum : |∑ i : Fin 3, A (vec2 (I := I) (basis i) (basis i))| ≤
        ∑ i : Fin 3, |A (vec2 (I := I) (basis i) (basis i))| := by
    simpa using
      (Finset.abs_sum_le_sum_abs (fun i : Fin 3 => A (vec2 (I := I) (basis i) (basis i))) Finset.univ)
  calc
    |∑ i : Fin 3, A (vec2 (I := I) (basis i) (basis i))| ≤
        ∑ i : Fin 3, |A (vec2 (I := I) (basis i) (basis i))| := hAbsSum
    _ ≤ ∑ i : Fin 3, C := by
      apply Finset.sum_le_sum
      intro i hi
      have h := hA (basis i)
      have hq : quad02 (I := I) (M := M) A (basis i) =
          A (vec2 (I := I) (basis i) (basis i)) := by
        rw [← eval02_self (I := I) (M := M) A (basis i)]
        unfold eval02 DifferentialGeometry.Geometry.Curvature.vec2
        rfl
      rw [hq] at h
      have hgi : g.inner x (basis i) (basis i) = 1 := by
        have hh := horth i i
        simpa [DifferentialGeometry.Geometry.Curvature.delta3] using hh
      rw [hgi] at h
      exact le_trans h (by rw [mul_one])
    _ = 3 * C := by
      simp

theorem hamiltonIveySupportUpperSec_eval_contOn
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {K a t0 T : Real} (hK : 0 < K) (ha : 0 < a) (ht0 : t0 ≤ 0)
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (x : M) (v w : TangentSpace I x) :
    ContinuousOn
      (fun t : Real =>
        twoTensorSecToFamily (I := I) (M := M)
          (hamiltonIveySupportUpperSec S K a t0) t x v w)
      (Set.Icc 0 T) := by
  have hcont :=
    tensorEval_contOn (I := I) (M := M)
      (hamiltonIveySupportUpperSecFamilyContinuousOnSet (I := I) S hS hK ha ht0 hTsub)
      x v w
  simpa [twoTensorSecToFamily] using hcont

theorem hamiltonIveySupportSmallBarrierLip_bound
    {δ C0 ccap c e gvv trS Svv : Real}
    (hden : 1 - 3 * δ ≠ 0) (hgvv : 0 ≤ gvv)
    (hcap : |c| ≤ ccap)
    (hSq : |Svv| ≤ C0 * gvv) (hTr : |trS| ≤ 3 * C0) :
    |e * ((2 * c / (1 - 3 * δ)) * gvv +
        ((2 * δ - 1) / (1 - 3 * δ)) * (trS * gvv - 3 * Svv))| ≤
      (2 * ccap / |1 - 3 * δ| + 6 * C0 * |(2 * δ - 1) / (1 - 3 * δ)|) * |e * gvv| := by
  have hdpos : 0 < |1 - 3 * δ| := abs_pos.mpr hden
  have hc1 : |2 * c / (1 - 3 * δ)| ≤ 2 * ccap / |1 - 3 * δ| := by
    rw [abs_div, abs_mul]
    rw [abs_of_nonneg (by positivity : 0 ≤ (2 : Real))]
    have hmul : 2 * |c| ≤ 2 * ccap := mul_le_mul_of_nonneg_left hcap (by positivity)
    rw [div_le_div_iff₀ hdpos hdpos]
    exact mul_le_mul_of_nonneg_right hmul (le_of_lt hdpos)
  have hB1 : |trS * gvv - 3 * Svv| ≤ 3 * C0 * gvv + 3 * C0 * gvv := by
    have habs : |trS * gvv - 3 * Svv| ≤ |trS * gvv| + |3 * Svv| := by
      simpa [abs_neg] using abs_add_le (trS * gvv) (-(3 * Svv))
    have h2 : |trS * gvv| ≤ |trS| * gvv := by
      rw [abs_mul, abs_of_nonneg hgvv]
    have h3 : |3 * Svv| ≤ 3 * |Svv| := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (3 : Real))]
    have h4 : |trS| * gvv ≤ 3 * C0 * gvv := by
      exact mul_le_mul_of_nonneg_right hTr hgvv
    have h5 : 3 * |Svv| ≤ 3 * (C0 * gvv) := by
      exact mul_le_mul_of_nonneg_left hSq (by positivity : 0 ≤ (3 : Real))
    nlinarith [habs, h2, h3, h4, h5]
  have hB : |((2 * δ - 1) / (1 - 3 * δ)) * (trS * gvv - 3 * Svv)| ≤
      6 * C0 * |(2 * δ - 1) / (1 - 3 * δ)| * gvv := by
    rw [abs_mul]
    calc
      |(2 * δ - 1) / (1 - 3 * δ)| * |trS * gvv - 3 * Svv| ≤
          |(2 * δ - 1) / (1 - 3 * δ)| * (3 * C0 * gvv + 3 * C0 * gvv) := by
        exact mul_le_mul_of_nonneg_left hB1 (abs_nonneg _)
      _ = 6 * C0 * |(2 * δ - 1) / (1 - 3 * δ)| * gvv := by ring
  have hA : |(2 * c / (1 - 3 * δ)) * gvv| ≤ 2 * ccap / |1 - 3 * δ| * gvv := by
    rw [abs_mul]
    rw [abs_of_nonneg hgvv]
    exact mul_le_mul_of_nonneg_right hc1 hgvv
  have hSum : |(2 * c / (1 - 3 * δ)) * gvv + ((2 * δ - 1) / (1 - 3 * δ)) * (trS * gvv - 3 * Svv)| ≤
      2 * ccap / |1 - 3 * δ| * gvv + 6 * C0 * |(2 * δ - 1) / (1 - 3 * δ)| * gvv := by
    exact (abs_add_le _ _).trans (add_le_add hA hB)
  calc
    |e * ((2 * c / (1 - 3 * δ)) * gvv + ((2 * δ - 1) / (1 - 3 * δ)) * (trS * gvv - 3 * Svv))| =
        |e| * |(2 * c / (1 - 3 * δ)) * gvv + ((2 * δ - 1) / (1 - 3 * δ)) * (trS * gvv - 3 * Svv)| := by
          rw [abs_mul]
    _ ≤ |e| * (2 * ccap / |1 - 3 * δ| * gvv + 6 * C0 * |(2 * δ - 1) / (1 - 3 * δ)| * gvv) := by
          exact mul_le_mul_of_nonneg_left hSum (abs_nonneg e)
    _ = (2 * ccap / |1 - 3 * δ| + 6 * C0 * |(2 * δ - 1) / (1 - 3 * δ)|) * |e| * gvv := by ring
    _ = (2 * ccap / |1 - 3 * δ| + 6 * C0 * |(2 * δ - 1) / (1 - 3 * δ)|) * |e * gvv| := by
          rw [abs_mul, abs_of_nonneg hgvv]
          ring

theorem hamiltonIveySupportUpperBarrierReg
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {K a t0 T : Real} (hK : 0 < K) (ha : 0 < a) (ht0 : t0 ≤ 0)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hTreg : Set.Ioc 0 T ⊆ D.regular) :
    TensorBarrierRegularityOn (I := I) (M := M)
      (fun t : Real => S.base.metric t)
      (twoTensorSecToFamily (I := I) (M := M)
        (hamiltonIveySupportUpperSec S K a t0))
      (fun _t x => (0 : TangentSpace I x))
      (hamiltonIveySupportUpperReact (I := I) (M := M) K a t0) T where
  tensor_eval_continuous := by
    intro x v w
    exact hamiltonIveySupportUpperSec_eval_contOn (I := I) S hS hK ha ht0 hTsub x v w
  metric_eval_continuous := by
    intro x v w
    simpa [SolutionOn.family] using
      ((hS.smoothMetric.coeff_cont x v w).mono hTsub)
  barrier_eval_continuous := by
    intro epsilon d tbar hsub x v w
    have hScont :
        ContinuousOn
          (fun t : Real =>
            twoTensorSecToFamily (I := I) (M := M)
              (hamiltonIveySupportUpperSec S K a t0) t x v w)
          (Set.Icc tbar (tbar + d)) :=
      (hamiltonIveySupportUpperSec_eval_contOn (I := I) S hS hK ha ht0 hTsub x v w).mono hsub
    have hGcont :
        ContinuousOn
          (fun t : Real => (S.base.metric t).inner x v w)
          (Set.Icc tbar (tbar + d)) := by
      exact
        (by
          simpa [SolutionOn.family] using
            ((hS.smoothMetric.coeff_cont x v w).mono hTsub) :
          ContinuousOn
            (fun t : Real => (S.base.metric t).inner x v w)
            (Set.Icc 0 T)).mono hsub
    have hcoef :
        ContinuousOn (fun t : Real => epsilon * (d + t - tbar))
          (Set.Icc tbar (tbar + d)) := by
      have hlin : Continuous (fun t : Real => d + t - tbar) :=
        (continuous_const.add continuous_id).sub continuous_const
      exact (continuous_const.mul hlin).continuousOn
    simpa [tensorBarrierFamily] using hScont.add (hcoef.mul hGcont)
  metricGainControl :=
    pinchMetricGain (I := I) (M := M) S hS hTsub hTreg
  smallBarrierLip := by
    intro delta0 tbar hdelta0 hsub0
    let δ : Real := hamiltonIveySupportPinchDelta a
    let ccap : Real := K * Real.exp (a + 2) / a
    have htbar0 : 0 ≤ tbar := (hsub0 ⟨le_rfl, by linarith⟩).1
    have hden0 : (1 : Real) - 3 * ((1 + a) / (2 * a)) ≠ 0 := by
      have hcalc : 1 - 3 * ((1 + a) / (2 * a)) = -(a + 3) / (2 * a) := by
        field_simp [ha.ne']
        ring
      rw [hcalc]
      have hnum : -(a + 3) ≠ 0 := by
        rw [neg_ne_zero]
        nlinarith
      exact div_ne_zero hnum (mul_ne_zero two_ne_zero ha.ne')
    have hden : (1 : Real) - 3 * δ ≠ 0 := by
      dsimp [δ]
      exact hden0
    have hdpos : 0 < |1 - 3 * δ| := abs_pos.mpr hden
    have hcpos : 0 < ccap := by
      dsimp [ccap]
      positivity
    rcases hamiltonIveySupportUpperSec_absBound_Icc (I := I) S hS hK ha ht0 hTsub
      (tstart := tbar) (t1 := tbar + delta0) (by intro t ht; exact hsub0 ht)
      with ⟨C0, hC0, hbound⟩
    refine ⟨2 * ccap / |1 - 3 * δ| + 6 * C0 * |(2 * δ - 1) / (1 - 3 * δ)|, ?_, ?_⟩
    · positivity
    · intro epsilon d hepsilon hd hdle t ht x v
      let e : Real := epsilon * (d + t - tbar)
      let g : SmoothRiemannianMetric I M := S.base.metric t
      let Sx : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
        (hamiltonIveySupportUpperSec S K a t0) t x
      let gvv : Real := g.inner x v v
      have htd0 : t ∈ Set.Icc tbar (tbar + delta0) :=
        ⟨ht.1, by linarith [ht.2, hdle]⟩
      have ht0' : 0 ≤ t - t0 := by
        linarith [ht.1]
      have hdiff := hamiltonIveySupportUpperReact_barrier_diff (I := I) S (ha := ha)
        (K := K) (epsilon := epsilon) (d := d) (t0 := t0) (tbar := tbar) (t := t)
        (x := x) (hdim := hdim x) v
      have hCvv :
          ((3 : Real) • shiftRic3At (I := I) (M := M) δ g
              (hamiltonIveySupportCoefficient K a t0 t • metricTensorField (I := I) g x - Sx) -
            metricTracePair0SAt (I := I) g
              (shiftRic3At (I := I) (M := M) δ g
                (hamiltonIveySupportCoefficient K a t0 t • metricTensorField (I := I) g x - Sx)) •
              metricTensorField (I := I) g x)
            (vec2 (I := I) v v) =
          metricTracePair0SAt (I := I) g Sx * gvv - (3 : Real) * Sx (vec2 (I := I) v v) := by
        dsimp [g, Sx, δ, gvv]
        rw [hamiltonIveySupportUpperReactLip_ltc_eq (I := I) S (ha := ha) (K := K)
          (a := a) (t0 := t0) (t := t) (x := x) (hdim := hdim x)]
        conv_lhs => rw [sub_eq_add_neg]
        change (metricTracePair0SAt (I := I) (S.base.metric t) ((hamiltonIveySupportUpperSec S K a t0) t x) •
              metricTensorField (I := I) (S.base.metric t) x) (vec2 (I := I) v v) +
            (-((3 : Real) • (hamiltonIveySupportUpperSec S K a t0) t x)) (vec2 (I := I) v v) =
          metricTracePair0SAt (I := I) (S.base.metric t) ((hamiltonIveySupportUpperSec S K a t0) t x) *
              ((S.base.metric t).inner x v v) -
            (3 : Real) * ((hamiltonIveySupportUpperSec S K a t0) t x) (vec2 (I := I) v v)
        simp only [Tensor0SSpace.smul_apply, Tensor0SSpace.neg_apply, metricTensorField_apply]
        have h0 : vec2 (I := I) v v 0 = v := by
          unfold DifferentialGeometry.Geometry.Curvature.vec2
          simp
        have h1 : vec2 (I := I) v v 1 = v := by
          unfold DifferentialGeometry.Geometry.Curvature.vec2
          norm_num
        rw [h0, h1]
        simp only [smul_eq_mul]
        ring
      have hgvv : 0 ≤ gvv := by
        by_cases hv : v = 0
        · subst v
          simp [gvv]
        · exact le_of_lt ((S.base.metric t).pos x v hv)
      have hc : |hamiltonIveySupportCoefficient K a t0 t| ≤ ccap := by
        dsimp [ccap]
        rw [abs_of_nonneg (le_of_lt (hamiltonIveySupportCoefficient_pos hK ha ht0'))]
        unfold hamiltonIveySupportCoefficient
        have hdenle : a ≤ a * (1 + 2 * K * (t - t0)) := by
          have h2 : 0 ≤ 2 * K * (t - t0) := by positivity
          have h3 : 0 ≤ a * (2 * K * (t - t0)) := mul_nonneg ha.le h2
          nlinarith
        have hnum0 : 0 ≤ K * Real.exp (a + 2) := by positivity
        exact div_le_div_of_nonneg_left hnum0 ha hdenle
      have hSq : |Sx (vec2 (I := I) v v)| ≤ C0 * gvv := by
        have hb := hbound t htd0 x v
        dsimp [Sx, gvv] at hb ⊢
        have hq : quad02 (I := I) (M := M) ((hamiltonIveySupportUpperSec S K a t0) t x) v =
            ((hamiltonIveySupportUpperSec S K a t0) t x) (vec2 (I := I) v v) := by
          simp [quad02, vec2_self_eq_const]
        rw [hq] at hb
        exact hb
      have hTr : |metricTracePair0SAt (I := I) g Sx| ≤ 3 * C0 := by
        exact hamiltonIveySupportUpperSec_trace_abs_le (I := I) g (hdim x) Sx (by
          intro u
          exact hbound t htd0 x u)
      have hmain := hamiltonIveySupportSmallBarrierLip_bound
        (δ := δ) (C0 := C0) (ccap := ccap) (c := hamiltonIveySupportCoefficient K a t0 t)
        (e := e) (gvv := gvv)
        (trS := metricTracePair0SAt (I := I) g Sx) (Svv := Sx (vec2 (I := I) v v))
        hden hgvv hc hSq hTr
      conv_lhs => rw [← neg_sub]
      rw [abs_neg]
      rw [hdiff]
      dsimp [g, Sx, δ] at hCvv
      rw [hCvv]
      simpa [e, gvv, g, Sx, δ] using hmain

end DifferentialGeometry.PDE.RicciFlow

end
