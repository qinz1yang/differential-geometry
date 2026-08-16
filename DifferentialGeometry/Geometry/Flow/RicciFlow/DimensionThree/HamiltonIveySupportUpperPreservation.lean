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

end DifferentialGeometry.PDE.RicciFlow

end
