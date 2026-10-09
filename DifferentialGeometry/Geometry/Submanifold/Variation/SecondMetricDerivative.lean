import DifferentialGeometry.Geometry.Comparison.Variation.LocalSecondVariation
import DifferentialGeometry.Geometry.Comparison.Variation.SecondVariation
import DifferentialGeometry.Geometry.Metric.SourceTangent

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry

open Riemannian Riemannian.Variation Riemannian.CovariantDerivativeAlong

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [I.Boundaryless] [T2Space M] in
private theorem centralAcceleration_eventuallyEq
    (g : SmoothRiemannianMetric I M)
    {d f : ℝ × ℝ → M} {t : ℝ} (h : d =ᶠ[𝓝 (0, t)] f) :
    ∀ᶠ u in 𝓝 t,
      (centralVariationAcceleration (I := I) g (Function.curry d) u : E) =
        (centralVariationAcceleration (I := I) g (Function.curry f) u : E) := by
  have hh : ∀ᶠ u in 𝓝 t, d =ᶠ[𝓝 (0, u)] f :=
    (continuous_const.prodMk continuous_id).continuousAt.eventually h.eventuallyEq_nhds
  filter_upwards [hh] with u hu
  have hs : (fun s : ℝ => d (s, u)) =ᶠ[𝓝 (0 : ℝ)] fun s => f (s, u) :=
    hu.comp_tendsto (continuous_id.prodMk continuous_const).continuousAt
  apply covDerivAlong_congr_curve g _ _ hs
  filter_upwards [hs.eventuallyEq_nhds] with s hderiv
  exact congrArg (fun L => L (1 : ℝ))
    (hderiv.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := I))

private theorem hasDerivAt_deriv_speedSq_local
    (g : SmoothRiemannianMetric I M)
    {f : ℝ × ℝ → M} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ f V)
    (hzero : (0, 0) ∈ V) :
    HasDerivAt (deriv (fun s => speedSq (I := I) g (Function.curry f) s 0))
      (2 * (indexFormIntegrand (I := I) g (fun u => f (0, u))
          (centralVariationField (I := I) (Function.curry f))
          (centralVariationField (I := I) (Function.curry f)) 0 +
        g.inner (f (0, 0))
          (covDerivAlong (I := I) g (fun u => f (0, u))
            (centralVariationAcceleration (I := I) g (Function.curry f)) 0)
          (centralVelocity (I := I) (Function.curry f) 0))) 0 := by
  obtain ⟨d, hd, heq⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_global_smooth_variation_eq_jointly_near_slice
      (L := 0) (s := 0) le_rfl hV (by simpa using hzero) hf
  have hjoint : d =ᶠ[𝓝 (0, 0)] f :=
    heq.self_of_nhds 0 ⟨le_rfl, le_rfl⟩
  have hd8 : IsSmoothVariation (I := I) (Function.curry d) := by
    unfold IsSmoothVariation
    have hh : ContMDiff 𝓘(ℝ, ℝ × ℝ) I (8 : ℕ) d := hd.of_le (by decide)
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hh
    exact hh
  have hfirst : (fun s => firstEnergyDensity (I := I) g (Function.curry d) s 0) =
      deriv (fun s => speedSq (I := I) g (Function.curry d) s 0) :=
    funext fun s => (firstEnergyDensity_hasDerivAt g (Function.curry d) hd8 s 0).deriv.symm
  have hsecond := secondEnergyDensity_hasDerivAt g (Function.curry d) hd8 0 0
  rw [hfirst] at hsecond
  have hformula :=
    secondEnergyDensity_zero_div_two_eq_indexFormIntegrand_add g (Function.curry d) hd8 0
  have hcoeff : secondEnergyDensity (I := I) g (Function.curry d) 0 0 =
      2 * (indexFormIntegrand (I := I) g (fun u => d (0, u))
          (centralVariationField (I := I) (Function.curry d))
          (centralVariationField (I := I) (Function.curry d)) 0 +
        g.inner (d (0, 0))
          (covDerivAlong (I := I) g (fun u => d (0, u))
            (centralVariationAcceleration (I := I) g (Function.curry d)) 0)
          (centralVelocity (I := I) (Function.curry d) 0)) := by
    exact ((div_eq_iff (by norm_num : (2 : ℝ) ≠ 0)).mp hformula).trans (mul_comm _ _)
  rw [hcoeff] at hsecond
  have hpath : (fun u => d (0, u)) =ᶠ[𝓝 (0 : ℝ)] fun u => f (0, u) :=
    hjoint.comp_tendsto (continuous_const.prodMk continuous_id).continuousAt
  have hfield := centralVariationField_eventuallyEq (I := I) hjoint
  have hacc := centralAcceleration_eventuallyEq (I := I) g hjoint
  have hgrad := covDerivAlong_congr_curve g
    (centralVariationField (I := I) (Function.curry d))
    (centralVariationField (I := I) (Function.curry f)) hpath hfield
  have hgradacc := covDerivAlong_congr_curve g
    (centralVariationAcceleration (I := I) g (Function.curry d))
    (centralVariationAcceleration (I := I) g (Function.curry f)) hpath hacc
  have hvel : centralVelocity (I := I) (Function.curry d) 0 =
      centralVelocity (I := I) (Function.curry f) 0 :=
    congrArg (fun L => L (1 : ℝ)) (hpath.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := I))
  have hbase := hjoint.eq_of_nhds
  let B : M → E → E → ℝ := fun p v w => g.inner p v w
  have hnorm := congrArg₂ (fun (p : M) (v : E) => B p v v) hbase hgrad
  have hcurvature := centralCurvatureDensity_eq_of_eventuallyEq (I := I) g hjoint
  have hindex : indexFormIntegrand (I := I) g (fun u => d (0, u))
      (centralVariationField (I := I) (Function.curry d))
      (centralVariationField (I := I) (Function.curry d)) 0 =
      indexFormIntegrand (I := I) g (fun u => f (0, u))
        (centralVariationField (I := I) (Function.curry f))
        (centralVariationField (I := I) (Function.curry f)) 0 :=
    congrArg₂ (fun a b : ℝ => a - b) hnorm hcurvature
  have hpair := congrArg₂ (fun (p : M) (vw : E × E) => B p vw.1 vw.2)
    hbase (congrArg₂ (fun (v w : E) => (v, w)) hgradacc hvel)
  have hspeed : (fun s => speedSq (I := I) g (Function.curry d) s 0) =ᶠ[𝓝 (0 : ℝ)]
      fun s => speedSq (I := I) g (Function.curry f) s 0 :=
    (speedSq_eventuallyEq g hjoint).comp_tendsto
      (continuous_id.prodMk continuous_const).continuousAt
  have hresult := hsecond.congr_of_eventuallyEq hspeed.deriv.symm
  exact hresult.congr_deriv
    (congrArg (fun r : ℝ => 2 * r) (congrArg₂ (fun a b : ℝ => a + b) hindex hpair))

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

theorem hasDerivAt_deriv_gramDiagonal_local
    (g : SmoothRiemannianMetric I M)
    {F : ℝ × A → M} {V : Set (ℝ × A)}
    (hV : IsOpen V) (hF : ContMDiffOn 𝓘(ℝ, ℝ × A) I ∞ F V)
    {z : A} (hz : (0, z) ∈ V) (v : A) :
    let f : ℝ → ℝ → M := fun t r => F (t, z + r • v)
    HasDerivAt (deriv (fun t => g.inner (F (t, z))
        (mfderiv 𝓘(ℝ, ℝ × A) I F (t, z) (0, v))
        (mfderiv 𝓘(ℝ, ℝ × A) I F (t, z) (0, v))))
      (2 * (indexFormIntegrand (I := I) g (f 0)
          (centralVariationField (I := I) f) (centralVariationField (I := I) f) 0 +
        g.inner (F (0, z))
          (covDerivAlong (I := I) g (f 0)
            (centralVariationAcceleration (I := I) g f) 0)
          (mfderiv 𝓘(ℝ, ℝ × A) I F (0, z) (0, v)))) 0 := by
  let L : ℝ × ℝ → ℝ × A := fun p => (p.1, z + p.2 • v)
  have hL : ContDiff ℝ ∞ L :=
    contDiff_fst.prodMk (contDiff_const.add (contDiff_snd.smul contDiff_const))
  let W := L ⁻¹' V
  have hW : IsOpen W := hV.preimage hL.continuous
  have hcomp : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (F ∘ L) W :=
    hF.comp hL.contMDiff.contMDiffOn (fun _ h => h)
  have hzero : (0, 0) ∈ W := by simpa [W, L] using hz
  have hh := hasDerivAt_deriv_speedSq_local g hW hcomp hzero
  have hpartial (t : ℝ) (ht : (t, z) ∈ V) :
      mfderiv 𝓘(ℝ, ℝ) I (fun r : ℝ => F (t, z + r • v)) 0 (1 : ℝ) =
        mfderiv 𝓘(ℝ, ℝ × A) I F (t, z) (0, v) := by
    have hd := ((hF (t, z) ht).contMDiffAt (hV.mem_nhds ht)).mdifferentiableAt (by simp)
    have hp := source_mfderiv_line hd ((0 : ℝ), v)
    have hline : (fun r : ℝ => F ((t, z) + r • ((0 : ℝ), v))) =
        fun r : ℝ => F (t, z + r • v) := by
      funext r
      apply congrArg F
      apply Prod.ext <;> simp
    have hderiv := congrArg
      (fun k : ℝ → M => (mfderiv 𝓘(ℝ, ℝ) I k 0 (1 : ℝ) : E)) hline
    exact hderiv.symm.trans hp
  let B : M → E → E → ℝ := fun p v w => g.inner p v w
  have hbase (t : ℝ) : F (t, z + (0 : ℝ) • v) = F (t, z) := by
    rw [zero_smul, add_zero]
  have htime : ∀ᶠ t in 𝓝 (0 : ℝ), (t, z) ∈ V :=
    (continuous_id.prodMk continuous_const).continuousAt (hV.mem_nhds hz)
  have hspeed : (fun t => speedSq (I := I) g (Function.curry (F ∘ L)) t 0) =ᶠ[𝓝 (0 : ℝ)]
      fun t => g.inner (F (t, z))
        (mfderiv 𝓘(ℝ, ℝ × A) I F (t, z) (0, v))
        (mfderiv 𝓘(ℝ, ℝ × A) I F (t, z) (0, v)) := by
    filter_upwards [htime] with t ht
    exact congrArg₂ (fun (p : M) (w : E) => B p w w) (hbase t) (hpartial t ht)
  have hresult := hh.congr_of_eventuallyEq hspeed.deriv.symm
  let f : ℝ → ℝ → M := fun t r => F (t, z + r • v)
  have hpair := congrArg₂ (fun (p : M) (w : E) =>
      B p (covDerivAlong (I := I) g (f 0)
        (centralVariationAcceleration (I := I) g f) 0) w)
    (hbase 0) (hpartial 0 hz)
  exact hresult.congr_deriv (congrArg (fun r : ℝ =>
    2 * (indexFormIntegrand (I := I) g (f 0)
      (centralVariationField (I := I) f) (centralVariationField (I := I) f) 0 + r)) hpair)

end DifferentialGeometry.Geometry
