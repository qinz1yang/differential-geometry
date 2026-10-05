import DifferentialGeometry.Geometry.Collapse.StaticRegisterV2
import DifferentialGeometry.Geometry.Collapse.StaticRegisterValidity
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LPA02UniformWitnesses
import DifferentialGeometry.Geometry.Fibration.GraphModelBlocks

/-!
# The closed threshold validity on the staged register: the core record (lane FC39-VAL2)

External review 52 (`docs/geometrization/chapter14/out/dispositions-task52-fc39-threshold-
validity.md`): validity is stated on `ClosedRegisterV2` (R-a), the family and every consumer use
the parameters the register records (no substitution), and the single-certificate chain keeps the
producer's PREFIX witnesses `εr, δ', Λz` before `T₀` (`T₀Low` uses the same `Λz`, `δ < δ'`) and
LPA02's FULL joint witness in the same chain, with the finite zero family selected from it.

This file is the CORE of the complete record, hence named `Partial…`: early constants (PR01–PR03
with CFS15 at the actual `Γ_j`), LC18, `I₁`, LPA01's standing clauses, and the joint package of the
producer-bound slots. The per-instance chapter-14 row fields follow in a later file.

* `GC.MetricGeometry.Cfs15ModulusAtV2 k K B Ξ Γ`: CFS15's conclusion (`cfs15_modulus_row`) at ONE
  value `Γ` (verbatim body of `Cfs15ModulusOut`), so that "the actual `Γ_j` lies in the native
  modulus range" is a field (`cfs15ModulusOut_iff_VAL2`).
* `Lpa02WitnessAtV2`, `Lpa02WitnessV2`: LPA02's per-scale and per-member joint witness
  (`lpa02_uniform_joint_zero_witnesses`, verbatim body; check `lpa02_witnessV2_VAL2`).
* `Lc18ExclusionOutV2 R M`: LC18's exclusion of a three-splitting of quality `β₃` on the normalized
  member at every scale of LPA01's window (from LC09's model at `σ_col`).
* `ClosedFamilyInstanceV2 K R M δ εr Λz`: the scale `ρ` in LPA01's window, the final family
  `LocalChartPacketsC14` with EXACTLY the register's values, LPA02's joint witness on the member at
  `(εr, e₀, T₀, V, δ)`, and the selection of every zero ball from that witness.
* `ClosedFamilyOnTailV2`, `ClosedFamilyAtV2`: prefix witness functions `εr, δ', Λz` of the values
  read before `T₀`, with `20 Λz ≤ T₀Low`, then one `δ < δ'` and on EVERY member of the register's
  tail one instance, LC09 at `σ_col` and LC18's exclusion on the same model.
* `PartialClosedThresholdValidityV2`: the core record; consumers below.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Bundle Function
open DifferentialGeometry DifferentialGeometry.Analysis GC.Endpoint
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Analysis.Calculus
open scoped BigOperators NNReal ContDiff Manifold Topology ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

namespace GC.MetricGeometry

/-- CFS15's conclusion (`cfs15_modulus_row`, verbatim) at ONE value `Γ` of the modulus range. -/
def Cfs15ModulusAtV2 (k K : ℕ) (B : ℝ) (Ξ : ℝ → ℝ) (Γ : ℝ) : Prop :=
  (∃ m : ℕ, Ξ Γ = (1 / 2 : ℝ) ^ (m + 4)) ∧
      ((∃ F : ℕ → ℝ, (∀ m, 0 ≤ F m) ∧
          ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
          δ₀ ≤ (Ξ Γ) / (3 * finiteCloudJetBudget F C K) ∧ Γ ≤ δ₀ ∧
          ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
            [FiniteDimensional ℝ H] (S T : Set H), S ⊆ T → TotallyBounded S →
            ∀ (r : H → ℝ) (P : H → Submodule ℝ H),
            (∀ x ∈ S, Module.finrank ℝ (P x) = k) →
            ∀ rmin R δ : ℝ, 0 < rmin →
            (∀ x ∈ S, rmin ≤ r x) → (∀ x ∈ S, r x ≤ R) →
            0 < δ → δ ≤ δ₀ →
            (∀ x ∈ T, ∀ y ∈ T, dist y x ≤ 128 * (Ξ Γ)⁻¹ * max (r y) (r x) →
              r x / B ≤ r y ∧ r y ≤ B * r x) →
            (∀ x ∈ S, hausdorffEDist (T ∩ ball x (r x / δ))
              ((AffineSubspace.mk' x (P x) : Set H) ∩ ball x (r x / δ)) ≤
                ENNReal.ofReal (δ * r x)) →
            ∃ (I : Set H) (hI : I.Finite), I ⊆ S ∧
              I.PairwiseDisjoint (fun i => ball i (r i)) ∧
              (∀ x ∈ S, ∃ i ∈ I, r x ≤ 2 * r i ∧ dist x i < 3 * r i) ∧
              ((⋃ x ∈ S, ball x (8 * (Ξ Γ)⁻¹ * r x)) ⊆
                ⋃ i ∈ I, ball i (20 * (Ξ Γ)⁻¹ * r i)) ∧
              let w : H → H → ℝ := fun i y =>
                  ballCutoff i (40 * (Ξ Γ)⁻¹ * r i) (2 * (40 * (Ξ Γ)⁻¹ * r i)) y /
                  (∑ a ∈ hI.toFinset,
                    ballCutoff a (40 * (Ξ Γ)⁻¹ * r a) (2 * (40 * (Ξ Γ)⁻¹ * r a)) y)
              let Q : H → Submodule ℝ H := fun y => ⨆ μ ∈ ball (1 : ℝ) (1 / 2),
                  Module.End.eigenspace
                  (∑ i ∈ hI.toFinset, w i y • (P i)ᗮ.starProjection).toLinearMap μ
              let η : H → H := fun y => (Q y).starProjection
                (y - ∑ i ∈ hI.toFinset, w i y • i)
              let U : Set H := ⋃ i ∈ I, ball i (20 * (Ξ Γ)⁻¹ * r i)
              let Z : Set H := {z | z ∈ U ∧ η z = 0}
              (IsProperMap (fun z : Z => (⟨z.1, z.2.1⟩ : U)) ∧
                ∃ cs : ChartedSpace (Fin k → ℝ) Z,
                  let _ := cs
                  IsManifold 𝓘(ℝ, Fin k → ℝ) ∞ Z ∧
                  _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) ∞
                    (Subtype.val : Z → H) ∧
                  let V : S → TopologicalSpace.Opens H := fun x => ⟨ball (x : H) (r x), isOpen_ball⟩
                  let Ω : TopologicalSpace.Opens H :=
                    ⟨⋃ x, (V x : Set H), isOpen_iUnion (fun x => (V x).isOpen)⟩
                  ∃ p : C^∞⟮𝓘(ℝ, H), Ω; 𝓘(ℝ, Fin k → ℝ), Z⟯,
                    _root_.Manifold.IsSubmersion 𝓘(ℝ, H) 𝓘(ℝ, Fin k → ℝ) ∞ p ∧
                    (∀ z : Ω, IsMinOn (fun y => dist (z : H) y) Z (p z : H) ∧
                      (∀ y ∈ Z, IsMinOn (fun w => dist (z : H) w) Z y → y = (p z : H))) ∧
                    (∀ x : S, ∀ z : V x,
                      ‖(p ⟨(z : H), mem_iUnion.mpr ⟨x, z.property⟩⟩ : H) -
                        ((x : H) + (P x).starProjection ((z : H) - x))‖ ≤ (Ξ Γ) * r x ∧
                      (let D : H →L[ℝ] H :=
                        mfderiv 𝓘(ℝ, H) 𝓘(ℝ, H) (fun y : Ω => (p y : H))
                          ⟨(z : H), mem_iUnion.mpr ⟨x, z.property⟩⟩
                      ‖D - (P x).starProjection‖ ≤ (Ξ Γ))) ∧
                    (let pAmbient : H → H := nearestAmbientExtension Ω Z p
                     ∀ x : S, ∀ z ∈ ball (x : H) (r x), ∀ j : ℕ,
                       ‖iteratedFDeriv ℝ j
                         (fun y => pAmbient y - ((x : H) + (P x).starProjection (y - x))) z‖ ≤
                           C j * δ * r x * ((r x)⁻¹) ^ j) ∧
                    (let pAmbient : H → H := nearestAmbientExtension Ω Z p
                     ∀ x : S, ∀ z ∈ ball (x : H) (r x), ∀ j ≤ K,
                       ‖iteratedFDeriv ℝ j
                         (fun y => pAmbient y - ((x : H) + (P x).starProjection (y - x))) z‖ ≤
                           ((Ξ Γ) / 3) * r x * ((r x)⁻¹) ^ j) ∧
                    (∀ z : Z, ∀ hz : (z : H) ∈ Ω, p ⟨(z : H), hz⟩ = z) ∧
                    (∀ x : S, ∀ z : Z, (z : H) ∈ ball (x : H) (r x) →
                      ‖actualZeroSetNormalProjector k Z z - (P x)ᗮ.starProjection‖ ≤ (Ξ Γ))) ∧
              (let N : Set H := ⋃ x ∈ S, ball x (r x);
                IsProperMap (Subtype.val : {z : N | (z : H) ∈ Z} → N)) ∧
              (Z ⊆ ⋃ q ∈ T, ball q ((Ξ Γ) * r q)) ∧
              (∀ x ∈ S,
                hausdorffEDist (((fun y => (r x)⁻¹ • (y - x)) '' T) ∩ closedBall 0 (Ξ Γ)⁻¹)
                    (((fun y => (r x)⁻¹ • (y - x)) '' Z) ∩ closedBall 0 (Ξ Γ)⁻¹) ≤
                    ENNReal.ofReal (7 * (Ξ Γ) / 16) ∧
                  hausdorffEDist (((fun y => (r x)⁻¹ • (y - x)) '' T) ∩ ball 0 (Ξ Γ)⁻¹)
                    (((fun y => (r x)⁻¹ • (y - x)) '' Z) ∩ ball 0 (Ξ Γ)⁻¹) ≤
                    ENNReal.ofReal (7 * (Ξ Γ) / 16)) ∧
              ∃ g : ∀ x : S, P x → (P x)ᗮ, ∀ x : S,
                ContDiffOn ℝ ∞ (g x) (ball 0 (4 * (Ξ Γ)⁻¹ * r x)) ∧
                (∀ t ∈ ball (0 : P x) (4 * (Ξ Γ)⁻¹ * r x), ‖g x t‖ ≤ r x / 4 ∧
                  (x : H) + orthogonalCoordinateSum (P x) (t, g x t) ∈ Z) ∧
                (∀ t ∈ ball (0 : P x) (4 * (Ξ Γ)⁻¹ * r x),
                  ∀ n ∈ closedBall (0 : (P x)ᗮ) (r x),
                  η ((x : H) + orthogonalCoordinateSum (P x) (t, n)) = 0 ↔ n = g x t) ∧
                (∀ m t, t ∈ ball (0 : P x) (4 * (Ξ Γ)⁻¹ * r x) → ∀ j, j ≤ m →
                  ‖iteratedFDeriv ℝ j (g x) t‖ ≤ F m * δ * r x * ((r x)⁻¹) ^ j) ∧
                Z ∩ ball (x : H) (3 * (Ξ Γ)⁻¹ * r x) =
                  {z : H | ∃ t ∈ ball (0 : P x) (4 * (Ξ Γ)⁻¹ * r x),
                    z = (x : H) + orthogonalCoordinateSum (P x) (t, g x t)} ∩
                      ball (x : H) (3 * (Ξ Γ)⁻¹ * r x) ∧
                (∀ t ∈ ball (0 : P x) (4 * (Ξ Γ)⁻¹ * r x), ∀ j ≤ K + 1,
                  ‖iteratedFDeriv ℝ j (g x) t‖ ≤ ((Ξ Γ) / 3) * r x * ((r x)⁻¹) ^ j)))

/-- `Cfs15ModulusOut` is `Cfs15ModulusAtV2` on the native range `(0, θ₁)`. -/
theorem cfs15ModulusOut_iff_VAL2 {k K : ℕ} {B : ℝ} {Ξ : ℝ → ℝ} :
    Cfs15ModulusOut k K B Ξ ↔ ∃ θ₁ : ℝ, 0 < θ₁ ∧ Tendsto Ξ (𝓝[>] 0) (𝓝 0) ∧
      ∀ Γ, 0 < Γ → Γ < θ₁ → Cfs15ModulusAtV2 k K B Ξ Γ :=
  Iff.rfl

end GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

open GC.MetricGeometry

universe u

/-- LPA02's joint witness at the point `p`, the radius `r` and the scale `s` (verbatim body of
`lpa02_uniform_joint_zero_witnesses`): model, cone, smooth `Ns`, curvature buffer on
`B(p, 400 s r)`, Kleiner–Lott `δ`-map at the scale `s r`, LC67's radial function with LC31's
cutoff, and the ball types. -/
def Lpa02WitnessAtV2 {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold I3 ∞ X]
    (g : SmoothRiemannianMetric I3 X) (K : ℕ) (ε e δ : ℝ) (p : X) (r s : ℝ)
    (hr : 0 < r) (hs : 0 < s) : Prop :=
  ∃ (N : Type) (mN : MetricSpace N) (cN : ChartedSpace E3 N),
    letI := mN
    letI := cN
    ∃ (_ : IsManifold I3 ∞ N)
      (G : ContMDiffRiemannianMetric I3 ((K - 1 : ℕ) : ℕ∞ω) E3 (TangentSpace I3 : N → Type _))
      (q : N),
      ProperSpace N ∧ ConnectedSpace N ∧
      (letI : RiemannianBundle (fun x : N => TangentSpace I3 x) := ⟨G.toRiemannianMetric⟩
       IsRiemannianManifold I3 N) ∧
      (∀ (x : N) (u₁ u₂ : TangentSpace I3 x), 0 ≤ G.sectionalCurvature x u₁ u₂) ∧
      fourPointComparison 0 (univ : Set N) ∧
      (∀ x y : N, ∃ f : Icc (0 : ℝ) 1 → N, Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧
        f ⟨1, by norm_num⟩ = y ∧ ∀ t₁ t₂, dist (f t₁) (f t₂) = dist x y * dist t₁ t₂) ∧
      ∃ (C : Type) (mC : MetricSpace C) (o : C), Nonempty (RadialConeData o) ∧
        ProperSpace C ∧
        (∀ τ : ℝ, 0 < τ → τ < 1 → ∃ R₀ : ℝ, ∀ R' : ℝ, ∀ hR' : 0 < R', R₀ ≤ R' →
          Nonempty (@KleinerLottApprox N C (mN.rescale R'⁻¹ (inv_pos.mpr hR')) mC q o τ)) ∧
      ∃ (Ns : Type) (_ : TopologicalSpace Ns) (_ : ChartedSpace E3 Ns)
        (_ : IsManifold I3 ∞ Ns) (_ : Ns ≃ₜ N),
        (∀ y ∈ Metric.ball p (400 * (s * r)),
          SectionalBoundedBelowAt g y (-((1 / 60) ^ 2 * (s * r)⁻¹ ^ 2))) ∧
        Nonempty (@KleinerLottApprox X C
          (mX.rescale (s * r)⁻¹ (inv_pos.mpr (mul_pos hs hr))) mC p o δ) ∧
        (letI := mX.rescale (s * r)⁻¹ (inv_pos.mpr (mul_pos hs hr))
        let gR := scaleMetric ((s * r)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (mul_pos hs hr)) 2) g
        ∃ F : X → ℝ, LipschitzWith (Real.toNNReal (1 + ε)) F ∧
          (∃ O : Set X, IsOpen O ∧ {x : X | 3 / 40 ≤ dist x p ∧ dist x p ≤ 11} ⊆ O ∧
            ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ F O) ∧
          (∀ x, |F x - Metric.infDist x {p}| < e) ∧
          (∀ x, x ∉ {x : X | 1 / 20 < dist x p ∧ dist x p < 20} →
            F x = Metric.infDist x {p}) ∧
          (∀ x y, |(F x - Metric.infDist x {p}) - (F y - Metric.infDist y {p})| ≤
            ε * dist x y) ∧
          (∀ x, 0 ≤ F x) ∧ F p = 0 ∧
          (∀ q' ∈ {x : X | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10},
            1 - ε ≤ Real.sqrt (gR.inner q' (gradFun gR F q') (gradFun gR F q')) ∧
              Real.sqrt (gR.inner q' (gradFun gR F q') (gradFun gR F q')) ≤ 1 + ε) ∧
          (∀ x, F x ∈ Icc (1 / 5 : ℝ) 2 → 1 / 5 - e < dist x p ∧ dist x p < 2 + e) ∧
          F ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ {x : X | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10} ∧
          (∃ O' : Set X, IsOpen O' ∧ F ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ O' ∧
            ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ F O' ∧ ∀ q' ∈ O', gradFun gR F q' ≠ 0) ∧
          ∃ L : ℝ, 0 ≤ L ∧ (∀ t, |deriv (annularCutoff cutoffProfile) t| ≤ L) ∧
            ContMDiff I3 𝓘(ℝ, ℝ) ∞ (fun x => annularCutoff cutoffProfile (F x)) ∧
            (∀ x, annularCutoff cutoffProfile (F x) ∈ Icc (0 : ℝ) 1) ∧
            (∀ x, F x ∈ Icc (3 / 10 : ℝ) (4 / 5) → annularCutoff cutoffProfile (F x) = 1) ∧
            tsupport (fun x => annularCutoff cutoffProfile (F x)) ⊆
              {x : X | 1 / 5 - e < dist x p ∧ dist x p < 9 / 10 + e} ∧
            ∀ q', Real.sqrt (gR.inner q'
              (gradFun gR (fun x => annularCutoff cutoffProfile (F x)) q')
              (gradFun gR (fun x => annularCutoff cutoffProfile (F x)) q')) ≤ L * (1 + ε)) ∧
        ∀ ρ' ∈ Icc (1 / 5 : ℝ) 2, ∃ Ψ : PartialDiffeomorph I3 I3 X Ns ∞,
          Ψ.source = Metric.ball p (ρ' * (s * r)) ∧ Ψ.target = univ

/-- LPA02's per-member joint witness: every point `p` and every radius `0 < r ≤ 2 r_p(w')` have
ONE scale `s ∈ [T, V]` carrying `Lpa02WitnessAtV2`. -/
def Lpa02WitnessV2 {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold I3 ∞ X]
    [CompactSpace X] (g : SmoothRiemannianMetric I3 X) (K : ℕ) (Λ w ε e T V δ : ℝ) : Prop :=
  ∀ (p : X) (r : ℝ) (hr : 0 < r), r ≤ 2 * firstVolumeScale g p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3)) →
    ∃ s ∈ Icc T V, ∃ hs : 0 < s, Lpa02WitnessAtV2 g K ε e δ p r s hr hs

/-- **Verbatim check of `Lpa02WitnessV2`**: LPA02 gives `V ≥ T`, `δ < δ'` and a tail of members
carrying the per-member joint witness. -/
theorem lpa02_witnessV2_VAL2
    {X : ℕ → Type} [∀ i, MetricSpace (X i)] [∀ i, ChartedSpace E3 (X i)]
    [∀ i, IsManifold I3 ∞ (X i)] [∀ i, CompactSpace (X i)]
    (g : ∀ i, SmoothRiemannianMetric I3 (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    {α : ℕ → ℝ} (hα : Tendsto α atTop atTop)
    (hstand : ∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
      curvatureRadius (g i) p) (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ → ℝ)
    (hA : ∀ C v, 0 < C → 0 < v → v < 4 * Real.pi / 3 → 0 < A C v)
    (hder : ∀ i (p : X i) v, 0 < v → v < 4 * Real.pi / 3 → (α i)⁻¹ ≤ v →
      ∀ C, 0 < C → C < α i → ∀ k ≤ K,
      ∀ y ∈ riemannianBallOf (g i) p (C * firstVolumeScale (g i) p v),
        curvatureDerivativeNorm (g i) k y ≤
          A C v * (firstVolumeScale (g i) p v ^ (k + 2))⁻¹)
    {Λ w : ℝ} (hΛ : 0 < Λ) (hw : 0 < w) (hwc : w < 4 * Real.pi / 3)
    {ε δ' e T : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hδ' : 0 < δ') (he : 0 < e)
    (he1 : e < 1 / 40) :
    ∃ V : ℝ, T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧
      ∀ᶠ i in atTop, Lpa02WitnessV2 (g i) K Λ w ε e T V δ :=
  lpa02_uniform_joint_zero_witnesses g hmetric hα hstand K hK A hA hder hΛ hw hwc hε hε1 hδ' he
    he1

/-- LC18's exclusion on the normalized member (PR12, B:10136): at every scale `ρ` of LPA01's window
at `(w, Λ)` of the register, the rescaled member has no three-splitting of quality `β₃`. -/
def Lc18ExclusionOutV2 {D : ClosedEarlyData} {T : ClosedThresholdsV2 D} (R : ClosedRegisterV2 D T)
    {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier}
    (M : ClosedModel W g) : Prop :=
  ∀ (p : M.X) (ρ : ℝ) (hρ : 0 < ρ), firstVolumeScale M.gX p R.later.scale.w / 2 ≤ ρ →
    ρ ≤ 2 * firstVolumeScale M.gX p (closedWPrime R.later.scale) →
    ¬ @HasEuclideanSplitting.{0, 0} M.X (M.mX.rescale ρ⁻¹ (inv_pos.mpr hρ)) p 3
      R.later.excl.β₃

/-- **LC18's exclusion from LC09's model** (bindable now): on a normalized model carrying LC09's
conclusion at `σ_col`, with `σ_col` and `β₃` in LC18's range, `Lc18ExclusionOutV2` holds. -/
theorem lc18ExclusionOutV2_of_lc09Out_VAL2 {D : ClosedEarlyData} {T : ClosedThresholdsV2 D}
    (R : ClosedRegisterV2 D T) {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} (M : ClosedModel W g)
    (hσ : R.later.err.σcol ≤ threeSplittingExclusionThreshold.{0, 0})
    (hβ : R.later.excl.β₃ ≤ threeSplittingExclusionThreshold.{0, 0})
    (h : Lc09Out R.later.err.σcol R.later.scale.Λ R.later.scale.w M) :
    Lc18ExclusionOutV2 R M := by
  intro p ρ hρ h1 h2
  obtain ⟨Y, mY, q, hc, -, hdim, hcomp, hseg, ⟨f⟩⟩ := h p ρ hρ h1 h2
  let := M.mX.rescale ρ⁻¹ (inv_pos.mpr hρ)
  exact threeSplittingExclusionThreshold_excludes q hseg hdim hcomp hσ hβ f

/-! ### The zero-model instances of a family (needed by every statement about `P.zero`) -/

section ZeroInstances

variable {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold I3 ∞ X] [CompactSpace X]
  {g : SmoothRiemannianMetric I3 X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The zero-model metrics of a `LocalChartPackets` family. -/
instance instMetricN_VAL2
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The zero-model atlases of a `LocalChartPackets` family. -/
instance instChartedN_VAL2
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The zero-cone metrics of a `LocalChartPackets` family. -/
instance instMetricC_VAL2
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

end ZeroInstances

/-- **One instance of the final family at the staged register `R`** on a normalized member model:
the scale `ρ` in LPA01's window at `w, Λ`, the family `LocalChartPacketsC14` with EXACTLY the
register's values (no substitution), LPA02's joint witness on the member at the family's `εr`,
`e = e₀`, `[T₀, V]` and cone error `δ`, and every zero ball selected from that witness. -/
structure ClosedFamilyInstanceV2 (K : ℕ) {D : ClosedEarlyData} {T : ClosedThresholdsV2 D}
    (R : ClosedRegisterV2 D T) {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} (M : ClosedModel W g) (δ εr Λz : ℝ) where
  /-- The scale. -/
  ρ : M.X → ℝ
  ρ_pos : ∀ p, 0 < ρ p
  /-- LPA01's window (C14P:259–260). -/
  ρ_bounds : ∀ p, firstVolumeScale M.gX p R.later.scale.w / 2 < ρ p ∧
    ρ p < 2 * firstVolumeScale M.gX p (closedWPrime R.later.scale)
  /-- The final family at the register's values. -/
  family : LocalChartPacketsC14 M.X M.gX M.hmetric ρ ρ_pos R.later.scale.Λ R.β R.later.excl.Δ
    R.later.err.co.qs K R.later.err.co.qe R.later.err.bd.μ R.later.split.b R.later.err.s
    R.later.err.wk.b' R.later.err.wk.s' R.later.err.co.ε R.later.circle.γc R.later.circle.βc
    R.later.Lmax R.later.err.bd.τ R.later.circle.γ δ εr R.later.err.co.e₀ R.later.split.T₀
    R.later.split.V R.later.err.co.ve R.later.err.co.ζ Λz
  /-- PR23 / LPA02: the full joint witness on this member, in the same chain. -/
  witness : Lpa02WitnessV2 M.gX K R.later.scale.Λ R.later.scale.w εr R.later.err.co.e₀
    R.later.split.T₀ R.later.split.V δ
  /-- The finite zero family is selected from that witness: every zero ball at `c` has radius
  `s ρ(c)` for a scale `s ∈ [T₀, V]` at which the joint witness at `(c, ρ(c))` holds. -/
  selected : ∀ c (hc : c ∈ family.zero.centres), ∃ s ∈ Icc R.later.split.T₀ R.later.split.V,
    ∃ hs : 0 < s, (family.zero.zero c hc).radius = s * ρ c ∧
      Lpa02WitnessAtV2 M.gX K εr R.later.err.co.e₀ δ c (ρ c) s (ρ_pos c) hs

/-- The single-certificate chain at `R` for given prefix witnesses `εr, δ', Λz` (review 52): the
witnesses' ranges, `20 Λz ≤ T₀Low` (the SAME `Λz`), then ONE `δ < δ'` and, on EVERY member of the
register's tail, a normalized model with one family instance, LC09 at `σ_col` and LC18's
exclusion. -/
def ClosedFamilyOnTailV2 (K : ℕ) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier) {D : ClosedEarlyData}
    {T : ClosedThresholdsV2 D} (R : ClosedRegisterV2 D T) (εr δ' Λz : ℝ) : Prop :=
  0 < εr ∧ εr < 1 / 4 ∧ εr < R.later.err.co.ε₀ ∧ 0 < δ' ∧ 0 < Λz ∧
    20 * Λz ≤ T.T₀Low R.stage R.later.circle R.later.excl R.later.err R.later.scale
      R.later.split.b R.later.split.β₁ ∧
    ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∀ m, R.later.tail ≤ m → ∃ M : ClosedModel (Wseq m) (gseq m),
      Nonempty (ClosedFamilyInstanceV2 K R M δ εr Λz) ∧
        Lc09Out R.later.err.σcol R.later.scale.Λ R.later.scale.w M ∧ Lc18ExclusionOutV2 R M

/-- **The joint `Out` of the producer-bound closed slots** (review 52, single-certificate row):
prefix witness FUNCTIONS `εr, δ', Λz` of the values a threshold reads before `T₀`
(`st, ci, ex, er, sc, b, β₁`), and at EVERY staged register the chain `ClosedFamilyOnTailV2`
with these witnesses. -/
def ClosedFamilyAtV2 (K : ℕ) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier) {D : ClosedEarlyData}
    (T : ClosedThresholdsV2 D) : Prop :=
  ∃ εrF δ'F ΛzF : ClosedStage D → ClosedCircleRequestsV2 → ClosedExclusions → ClosedErrorsV2 →
      ClosedScales → ℝ → ℝ → ℝ,
    ∀ R : ClosedRegisterV2 D T,
      ClosedFamilyOnTailV2 K Wseq gseq R
        (εrF R.stage R.later.circle R.later.excl R.later.err R.later.scale R.later.split.b
          R.later.split.β₁)
        (δ'F R.stage R.later.circle R.later.excl R.later.err R.later.scale R.later.split.b
          R.later.split.β₁)
        (ΛzF R.stage R.later.circle R.later.excl R.later.err R.later.scale R.later.split.b
          R.later.split.β₁)

/-- **The core of the closed threshold validity on the staged register** (review 52; PARTIAL: the
per-instance chapter-14 row fields are added by the complete record). Every slot is bound to the
analytic conclusion of its native declaration at the chosen value, on the given standing sequence.
-/
structure PartialClosedThresholdValidityV2 (K : ℕ) (A : ℝ → ℝ) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (D : ClosedEarlyData) (T : ClosedThresholdsV2 D) : Prop where
  /-- PR01 `N`: GAF01's multiplicity `⌊fc07ActiveBound⌋₊` (every active-tag count of `𝓔⁰`). -/
  N_ge : gafMultiplicity ≤ D.N
  /-- PR01 `P`: CGP02's profile bound. -/
  P_ge : cgpProfileBound ≤ D.P
  /-- PR01 `P`: the slim/edge/circle graph-model profile bound (SGP04, EGP06, TCP05). -/
  P_ge_sgp : sgpProfileBound ≤ D.P
  /-- PR01 `P`: the zero graph-model profile bound. -/
  P_ge_zero : zeroProfileBound ≤ D.P
  /-- PR02 `L₀`: CGP02's global derivative bound of the initial map. -/
  L₀_ge : gafDerivativeBound ≤ D.L₀
  /-- PR03 `Ξ_j`: CFS15's full conclusion for the chosen modulus at the stage dimension `k_j`, jet
  order `K`, ratio `B = 5/3` (GAF01, `ActualAdjustmentChoice.lean:96`). -/
  Ξ_cfs15 : ∀ j, Cfs15ModulusOut (gafStageDim j) K (5 / 3) (D.Ξ j)
  /-- PR03: every actual `Γ_j` of every stage choice lies in CFS15's native range. -/
  Ξ_range : ∀ (st : ClosedStage D) j, Cfs15ModulusAtV2 (gafStageDim j) K (5 / 3) (D.Ξ j) (st.Γ j)
  /-- PR12 `lc18`: LC18's obstruction (the producer's `β 3 ≤ thr`, C14P:240). -/
  lc18_le : T.lc18 ≤ threeSplittingExclusionThreshold.{0, 0}
  /-- PR20 `I₁`: the comparison constant of `v_* = w'/(24 I(1))` (LPA02's volume constant). -/
  I₁_eq : T.I₁ = ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2
  /-- PR24 `H`: LPA01's standing clauses at `α = T.H` (the producer's `hstand`, `hder`,
  C14P:249–255, with `A' = boundaryDerivativeConstant A K`) on every member. -/
  standing : ∀ m (p : (Wseq m).Carrier),
    ENNReal.ofReal (T.H m * firstVolumeScale (gseq m) p (T.H m)⁻¹) ≤ curvatureRadius (gseq m) p ∧
    ∀ v, 0 < v → v < 4 * Real.pi / 3 → (T.H m)⁻¹ ≤ v → ∀ C, 0 < C → C < T.H m → ∀ k ≤ K,
      ∀ y ∈ riemannianBallOf (gseq m) p (C * firstVolumeScale (gseq m) p v),
        curvatureDerivativeNorm (gseq m) k y ≤
          boundaryDerivativeConstant A K C v * (firstVolumeScale (gseq m) p v ^ (k + 2))⁻¹
  /-- PR11–PR25: the joint package of the producer-bound slots (closed members). -/
  family : (∀ m, ClosedMemberFacts (Wseq m)) → ClosedFamilyAtV2 K Wseq gseq T

namespace PartialClosedThresholdValidityV2

variable {K : ℕ} {A : ℝ → ℝ} {Wseq : ℕ → CompactCarrier.{u}}
  {gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier}
  {D : ClosedEarlyData} {T : ClosedThresholdsV2 D}

/-- **Consumer (wrapper (1) shape, family level)**: at every staged register, one tail
`N ≥ R.later.tail` on which every member carries the final family at `R`, with `20 Λz ≤ T₀`. -/
theorem exists_family_on_tail_VAL2 (hv : PartialClosedThresholdValidityV2 K A Wseq gseq D T)
    (hf : ∀ m, ClosedMemberFacts (Wseq m)) (R : ClosedRegisterV2 D T) :
    ∃ N : ℕ, R.later.tail ≤ N ∧ ∃ δ εr Λz : ℝ, 20 * Λz ≤ R.later.split.T₀ ∧ ∀ m, N ≤ m →
      ∃ M : ClosedModel (Wseq m) (gseq m), Nonempty (ClosedFamilyInstanceV2 K R M δ εr Λz) := by
  obtain ⟨εrF, δ'F, ΛzF, h⟩ := hv.family hf
  obtain ⟨-, -, -, -, -, hT, δ, -, -, ht⟩ := h R
  refine ⟨R.later.tail, le_rfl, δ, _, _, hT.trans ((le_max_right _ _).trans R.later.T₀_ge),
    fun m hm => (ht m hm).imp fun _ hM => hM.1⟩

/-- **Consumer (H transport)**: the standing clauses transported to ANY normalized model of a
member — exactly the producer's `hstand` and `hder` on the model sequence. -/
theorem standing_on_model_VAL2 (hv : PartialClosedThresholdValidityV2 K A Wseq gseq D T)
    (m : ℕ) (M : ClosedModel (Wseq m) (gseq m)) (p : M.X) :
    ENNReal.ofReal (T.H m * firstVolumeScale M.gX p (T.H m)⁻¹) ≤ curvatureRadius M.gX p ∧
    ∀ v, 0 < v → v < 4 * Real.pi / 3 → (T.H m)⁻¹ ≤ v → ∀ C, 0 < C → C < T.H m → ∀ k ≤ K,
      ∀ y ∈ riemannianBallOf M.gX p (C * firstVolumeScale M.gX p v),
        curvatureDerivativeNorm M.gX k y ≤
          boundaryDerivativeConstant A K C v * (firstVolumeScale M.gX p v ^ (k + 2))⁻¹ := by
  obtain ⟨h1, h2⟩ := hv.standing m (M.ψ p)
  refine ⟨by rw [M.firstVolumeScale_eq, M.curvatureRadius_eq]; exact h1, ?_⟩
  intro v hv0 hvc hvH C hC hCH k hk y hy
  rw [M.ball_eq_preimage, M.firstVolumeScale_eq] at hy
  rw [M.curvatureDerivativeNorm_eq, M.firstVolumeScale_eq]
  exact h2 v hv0 hvc hvH C hC hCH k hk (M.ψ y) hy

/-- **Consumer (LC18)**: the splitting coordinate `β 3 = β₃` of the family at `R` is below LC18's
obstruction. -/
theorem β_three_le_VAL2 (hv : PartialClosedThresholdValidityV2 K A Wseq gseq D T)
    (R : ClosedRegisterV2 D T) : R.β 3 ≤ threeSplittingExclusionThreshold.{0, 0} := by
  rw [ClosedRegisterV2.β_three_VAL2]
  exact (R.later.β₃_lt.trans_le hv.lc18_le).le

/-- **Consumer (PR03)**: the accuracy `ε_j = Ξ_j(Γ_j)` of the actual stage choice is a value of
CFS15's dyadic modulus. -/
theorem Ξ_dyadic_VAL2 (hv : PartialClosedThresholdValidityV2 K A Wseq gseq D T)
    (st : ClosedStage D) (j : Fin 3) : ∃ n : ℕ, D.Ξ j (st.Γ j) = (1 / 2 : ℝ) ^ (n + 4) :=
  (hv.Ξ_range st j).1

/-- **Consumer (I₁)**: the register's `v_*` is LPA02's volume constant
`w' / (24 ∫₀¹ sinh²)`. -/
theorem vStar_eq_VAL2 (hv : PartialClosedThresholdValidityV2 K A Wseq gseq D T)
    (R : ClosedRegisterV2 D T) :
    closedVStarV2 T R.later.scale = R.later.scale.w / (2 * (1 + 2 * R.later.scale.Λ⁻¹) ^ 3) /
      (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) := by
  rw [closedVStarV2, hv.I₁_eq, closedWPrime]

end PartialClosedThresholdValidityV2

end DifferentialGeometry.Geometry.Collapse
