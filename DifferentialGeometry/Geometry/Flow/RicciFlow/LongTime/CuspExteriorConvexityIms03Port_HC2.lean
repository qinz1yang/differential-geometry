/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/

import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspExteriorCollars
import DifferentialGeometry.Geometry.Hyperbolic.Cusp.Convexity
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.RawRestriction
import DifferentialGeometry.Geometry.Metric.PullbackScaling
import DifferentialGeometry.Geometry.Operator.HessianAlgebra
import DifferentialGeometry.Topology.Manifold.OpenEmbedding
import DifferentialGeometry.Geometry.Operator.JetComparison

/-!
# S-MIRRORS port of IMS03 `CuspExteriorConvexity` (`_HC2`)

This is `DifferentialGeometry/Geometry/Flow/RicciFlow/LongTime/CuspExteriorConvexity.lean` of branch
`gc/juihuichung/ims03-astra-20261005` (tip `f49e541fb`), with six local repairs of elaboration
details (no statement, no definition and no proof idea is altered):
* `DifferentialGeometry.isLocalDiffeomorphAt_of_comp` with named arguments `(f := ...) (x := ...)`
  (this tree also has `DifferentialGeometry.Topology.Manifold.isLocalDiffeomorphAt_of_comp`);
* `rw [le_inv_comm₀ two_pos _]` instead of the nonexistent `le_inv_iff₀`;
* `let` instead of `letI`, `_hU` for two unused binders, `mem_ofPred_eq` for the deprecated
  `mem_setOf_eq` (lint cleanups).
The main theorem is `GC.LongTime.PersistentCuspExterior.exists_eventual_convex_profiles`.
The module `CuspExteriorConvexity` (the IMS03 path) is a shim re-exporting this file; this file
imports the module `CuspExteriorCollars`, itself a shim of the port of the IMS03 file.
-/

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set DifferentialGeometry
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.VectorField
open scoped Manifold ContDiff



open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Topology DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
open scoped Topology

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff

namespace GC.LongTime

universe u

namespace PersistentHyperbolicCores

variable {P : OrientedThreeStage.{u}} {g : P.Metric}
  {F : GC.Interface.RawSurgery P g} {K : ℕ}

/-- Restricting the original persistent core map to an open subset of its
actual domain gives a local diffeomorphism. -/
theorem map_isLocalDiffeomorph_on_open
    (C : PersistentHyperbolicCores F K) (i : Fin C.count)
    (t : ℝ) (ht : C.start ≤ t) (U : Opens (C.model i).Carrier)
    (hU : (U : Set (C.model i).Carrier) ⊆ C.domain i t) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fun x : U => C.map i t ht x) := by
  have he := C.embedding i t ht
  have hfull : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (fun x : C.domain i t => C.map i t ht x) :=
    isLocalDiffeomorph_of_injective_mfderiv _ he.contMDiff
      (fun x => (he.isImmersion.isImmersionAt x).mfderiv_injective (by simp)) rfl
  apply isLocalDiffeomorph_restrict_open U
  intro x
  exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp
    (f := (Subtype.val : C.domain i t → (C.model i).Carrier)) (x := ⟨x, hU x.property⟩)
    (hfull ⟨x, hU x.property⟩)
    (isLocalDiffeomorph_subtype_val (C.domain i t) ⟨x, hU x.property⟩)

/-- The actual persistent raw metric error is the derivative norm of the
normalized original `postMetric` on the same fixed open source. -/
theorem metricDerivNorm_normalized_pullback_lt
    (C : PersistentHyperbolicCores F K) (i : Fin C.count)
    (t : ℝ) (ht : C.start ≤ t) (U : Opens (C.model i).Carrier)
    (hU : (U : Set (C.model i).Carrier) ⊆ C.domain i t)
    (x : U)
    (hx : (x : (C.model i).Carrier) ∈ riemannianBallOf
      (C.model i).metric (C.model i).basepoint (C.accuracy t)⁻¹)
    (k : ℕ) (hk : k ≤ max K ⌈(C.accuracy t)⁻¹⌉₊) :
    metricDerivNorm k
      (localPullMetric
        (scaleMetric t⁻¹ (inv_pos.mpr (C.start_pos.trans_le ht))
          (postMetric F.observation t))
        (fun y : U => C.map i t ht y)
        (C.map_isLocalDiffeomorph_on_open i t ht U hU))
      ((C.model i).metric.restrictOpen U)
      ((C.model i).metric.restrictOpen U) x < C.accuracy t := by
  rw [metricDerivNorm_scaled_localPullMetric_eq_raw (C.model i).metric
    (postMetric F.observation t) (C.map i t ht) U
    (C.map_isLocalDiffeomorph_on_open i t ht U hU)
    t⁻¹ (inv_pos.mpr (C.start_pos.trans_le ht)) k x]
  exact C.metric_error i t ht k hk x hx

/-- All orders through two are supplied at late times, independently of the
fixed value of `K`. The open set and the point remain unchanged. -/
theorem metricDerivNorm_normalized_pullback_lt_of_le_two
    (C : PersistentHyperbolicCores F K) (i : Fin C.count)
    (t : ℝ) (ht : C.start ≤ t) (U : Opens (C.model i).Carrier)
    (hU : (U : Set (C.model i).Carrier) ⊆ C.domain i t)
    (ha : C.accuracy t < 1 / 2) (x : U)
    (hx : (x : (C.model i).Carrier) ∈ riemannianBallOf
      (C.model i).metric (C.model i).basepoint (C.accuracy t)⁻¹)
    (k : ℕ) (hk : k ≤ 2) :
    metricDerivNorm k
      (localPullMetric
        (scaleMetric t⁻¹ (inv_pos.mpr (C.start_pos.trans_le ht))
          (postMetric F.observation t))
        (fun y : U => C.map i t ht y)
        (C.map_isLocalDiffeomorph_on_open i t ht U hU))
      ((C.model i).metric.restrictOpen U)
      ((C.model i).metric.restrictOpen U) x < C.accuracy t := by
  have hinv : (2 : ℝ) ≤ (C.accuracy t)⁻¹ := by
    rw [le_inv_comm₀ two_pos (C.accuracy_pos t ht)]
    linarith
  have hceil : (2 : ℝ) ≤ (⌈(C.accuracy t)⁻¹⌉₊ : ℝ) :=
    hinv.trans (Nat.le_ceil _)
  have hnat : 2 ≤ ⌈(C.accuracy t)⁻¹⌉₊ := by exact_mod_cast hceil
  exact C.metricDerivNorm_normalized_pullback_lt i t ht U hU x hx k
    (hk.trans (hnat.trans (le_max_right _ _)))

/-- Multiplying the normalized pullback by the same physical time recovers
the pullback of the original `postMetric`, as an equality of metrics. -/
theorem scale_normalized_pullback_eq
    (C : PersistentHyperbolicCores F K) (i : Fin C.count)
    (t : ℝ) (ht : C.start ≤ t) (U : Opens (C.model i).Carrier)
    (hU : (U : Set (C.model i).Carrier) ⊆ C.domain i t) :
    scaleMetric t (C.start_pos.trans_le ht)
      (localPullMetric
        (scaleMetric t⁻¹ (inv_pos.mpr (C.start_pos.trans_le ht))
          (postMetric F.observation t))
        (fun y : U => C.map i t ht y)
        (C.map_isLocalDiffeomorph_on_open i t ht U hU)) =
      localPullMetric (postMetric F.observation t)
        (fun y : U => C.map i t ht y)
        (C.map_isLocalDiffeomorph_on_open i t ht U hU) := by
  rw [localPullMetric_scaleMetric]
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  simp only [scaleMetric_inner]
  rw [← mul_assoc, mul_inv_cancel₀ (C.start_pos.trans_le ht).ne', one_mul]

/-- Constant positive time normalization does not change the covariant
Hessian of any scalar on this same open source. -/
theorem hessFun_normalized_pullback_eq
    (C : PersistentHyperbolicCores F K) (i : Fin C.count)
    (t : ℝ) (ht : C.start ≤ t) (U : Opens (C.model i).Carrier)
    (hU : (U : Set (C.model i).Carrier) ⊆ C.domain i t)
    (ρ : U → ℝ) (x : U) :
    hessFun
      (localPullMetric
        (scaleMetric t⁻¹ (inv_pos.mpr (C.start_pos.trans_le ht))
          (postMetric F.observation t))
        (fun y : U => C.map i t ht y)
        (C.map_isLocalDiffeomorph_on_open i t ht U hU)) ρ x =
      hessFun (localPullMetric (postMetric F.observation t)
        (fun y : U => C.map i t ht y)
        (C.map_isLocalDiffeomorph_on_open i t ht U hU)) ρ x := by
  rw [localPullMetric_scaleMetric, hessFun_scaleMetric]


/-- The scalar germ on the fixed open buffer has exactly the physical
covariant Hessian after applying the derivative of the original core map.
Positive time normalization introduces no factor in this identity. -/
theorem hessFun_postMetric_eq_normalized_pullback_of_germ
    (C : PersistentHyperbolicCores F K) (i : Fin C.count)
    (t : ℝ) (ht : C.start ≤ t) (U : Opens (C.model i).Carrier)
    (hU : (U : Set (C.model i).Carrier) ⊆ C.domain i t)
    (ρ : C^∞⟮𝓡 3, (postStage F.observation t).Carrier; ℝ⟯)
    (σ : U → ℝ) (x : U)
    (hσ : σ =ᶠ[nhds x] fun y : U => ρ (C.map i t ht y))
    (v w : TangentSpace (𝓡 3) x) :
    hessFun (postMetric F.observation t) ρ (C.map i t ht x)
        (mfderiv (𝓡 3) (𝓡 3) (fun y : U => C.map i t ht y) x v)
        (mfderiv (𝓡 3) (𝓡 3) (fun y : U => C.map i t ht y) x w) =
      hessFun
        (localPullMetric
          (scaleMetric t⁻¹ (inv_pos.mpr (C.start_pos.trans_le ht))
            (postMetric F.observation t))
          (fun y : U => C.map i t ht y)
          (C.map_isLocalDiffeomorph_on_open i t ht U hU)) σ x v w := by
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) U.isOpen)
  rw [C.hessFun_normalized_pullback_eq i t ht U hU σ x]
  rw [DifferentialGeometry.Geometry.Connection.hessFun_congr _ hσ]
  exact (hessFun_localPull (postMetric F.observation t)
    (fun y : U => C.map i t ht y)
    (C.map_isLocalDiffeomorph_on_open i t ht U hU) ρ x v w).symm

/-- Full positivity on a fixed normalized buffer transfers to the original
physical metric at its image point. The scalar germ and the derivative
isomorphism both use the same original persistent core map. -/
theorem hessFun_postMetric_pos_of_normalized_pullback_germ
    (C : PersistentHyperbolicCores F K) (i : Fin C.count)
    (t : ℝ) (ht : C.start ≤ t) (U : Opens (C.model i).Carrier)
    (hU : (U : Set (C.model i).Carrier) ⊆ C.domain i t)
    (ρ : C^∞⟮𝓡 3, (postStage F.observation t).Carrier; ℝ⟯)
    (σ : U → ℝ) (x : U)
    (hσ : σ =ᶠ[nhds x] fun y : U => ρ (C.map i t ht y))
    (hpos : ∀ v : TangentSpace (𝓡 3) x, v ≠ 0 →
      0 < hessFun
        (localPullMetric
          (scaleMetric t⁻¹ (inv_pos.mpr (C.start_pos.trans_le ht))
            (postMetric F.observation t))
          (fun y : U => C.map i t ht y)
          (C.map_isLocalDiffeomorph_on_open i t ht U hU)) σ x v v)
    (V : TangentSpace (𝓡 3) (C.map i t ht x)) (hV : V ≠ 0) :
    0 < hessFun (postMetric F.observation t) ρ (C.map i t ht x) V V := by
  let hf := C.map_isLocalDiffeomorph_on_open i t ht U hU
  let v : TangentSpace (𝓡 3) x :=
    (hf.mfderivToContinuousLinearEquiv (by simp) x).symm V
  have hpush :
      mfderiv (𝓡 3) (𝓡 3) (fun y : U => C.map i t ht y) x v = V := by
    rw [← hf.mfderivToContinuousLinearEquiv_coe (by simp)]
    exact (hf.mfderivToContinuousLinearEquiv (by simp) x).apply_symm_apply V
  have hv : v ≠ 0 := by
    intro hv
    apply hV
    rw [← hpush, hv, map_zero]
  have hessian := C.hessFun_postMetric_eq_normalized_pullback_of_germ
    i t ht U hU ρ σ x hσ v v
  rw [hpush] at hessian
  rw [hessian]
  exact hpos v hv

end PersistentHyperbolicCores

end GC.LongTime


open DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Geometry.Hyperbolic.CuspConvexity
open DifferentialGeometry.Topology
open GC.Endpoint

namespace GC.LongTime

universe u

/-- The original cusp collar supplies a compact signed band and a positive
raw-metric tolerance before time is introduced. At a point of that same band,
the actual persistent metric error and the profile germ imply full Hessian
positivity for the original physical `postMetric`. -/
theorem PersistentCuspExterior.exists_compact_cusp_postMetric_hessian_tolerance
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ}
    {C : PersistentHyperbolicCores F K} (E : PersistentCuspExterior C)
    (i : Fin C.count) (j : Fin (E.truncation i).count)
    (d : SmoothTwoSidedCollar torusModel (𝓡 3)
      (fun s => (E.truncation i).cuspMap j (s, halfZero)))
    (heq : ∀ (p : Torus × symmetricOpenInterval d.radius) (hp : 0 ≤ p.2.val),
      d.toFun p = (E.truncation i).cuspMap j (p.1, halfPoint p.2.val hp)) :
    ∃ δ ε : ℝ, 0 < δ ∧ δ < d.radius ∧ 0 < ε ∧ ε ≤ 1 / 2 ∧
      let B : Set d.neighborhood :=
        {q | |collarHeight (C.model i) (E.truncation i) j d q| ≤ δ}
      IsCompact B ∧
      ∀ (t : ℝ) (ht : E.start ≤ t)
        (_hU : (d.neighborhood : Set (C.model i).Carrier) ⊆ C.domain i t),
        C.accuracy t < ε →
        ∀ (ρ : C^∞⟮𝓡 3, (postStage F.observation t).Carrier; ℝ⟯)
          (x : d.neighborhood), x ∈ B →
          (x : (C.model i).Carrier) ∈ riemannianBallOf
            (C.model i).metric (C.model i).basepoint (C.accuracy t)⁻¹ →
          (collarRho (C.model i) (E.truncation i) j d =ᶠ[nhds x]
            fun y : d.neighborhood => ρ (C.map i t (E.after_cores.trans ht) y)) →
          ∀ V : TangentSpace (𝓡 3) (C.map i t (E.after_cores.trans ht) x), V ≠ 0 →
            0 < hessFun (postMetric F.observation t) ρ
              (C.map i t (E.after_cores.trans ht) x) V V := by
  obtain ⟨δ, ε, hδ, hδd, hεpos, hε, hB, hmargin⟩ :=
    exists_compact_cusp_hessian_margin (C.model i) (E.truncation i) j d heq
  refine ⟨δ, ε, hδ, hδd, hεpos, hε, hB, ?_⟩
  intro t ht hU hα ρ x hx hxball hρ V hV
  have hstart : C.start ≤ t := E.after_cores.trans ht
  have hhalf : C.accuracy t < 1 / 2 := hα.trans_le hε
  apply C.hessFun_postMetric_pos_of_normalized_pullback_germ
    i t hstart d.neighborhood hU ρ
    (collarRho (C.model i) (E.truncation i) j d) x hρ ?_ V hV
  intro v hv
  let g₀ := (C.model i).metric.restrictOpen d.neighborhood
  let σ := collarRho (C.model i) (E.truncation i) j d
  let h := localPullMetric
    (scaleMetric t⁻¹ (inv_pos.mpr (C.start_pos.trans_le hstart))
      (postMetric F.observation t))
    (fun y : d.neighborhood => C.map i t hstart y)
    (C.map_isLocalDiffeomorph_on_open i t hstart d.neighborhood hU)
  have hsmall : ∀ k : ℕ, k ≤ 1 → metricDerivNorm k h g₀ g₀ x ≤ ε := by
    intro k hk
    exact (C.metricDerivNorm_normalized_pullback_lt_of_le_two
      i t hstart d.neighborhood hU hhalf x hxball k (hk.trans (by norm_num))).le.trans hα.le
  have hdiff := abs_hessFun_sub_le_of_small_metric_derivatives g₀ h σ
    (collarRho_smooth (C.model i) (E.truncation i) j d) x ε hε hsmall v v
  obtain ⟨hmarginx, hgradx⟩ := hmargin x hx v hv
  have habs : |hessFun h σ x v v - hessFun g₀ σ x v v| ≤
      (1 / 8 : ℝ) * g₀.inner x v v := by
    calc
      _ ≤ 12 * ε * Real.sqrt (normGradSqFun g₀ σ x) * g₀.inner x v v := by
        simpa only [normGradSqFun_def, mul_assoc,
          Real.mul_self_sqrt (metric_inner_self_nonneg g₀ x v)] using hdiff
      _ ≤ _ := hgradx
  have hlow := (abs_le.mp habs).1
  have hmetric : 0 < g₀.inner x v v := g₀.pos x v hv
  change 0 < hessFun h σ x v v
  change (1 / 4 : ℝ) * g₀.inner x v v < hessFun g₀ σ x v v at hmarginx
  linarith

end GC.LongTime

open Filter
open scoped Topology

namespace GC.LongTime

universe u

/-- A finite family of the original cusp collars admits one profile radius and
one positive metric-error tolerance before physical time is introduced. The
compact bands and the physical Hessian conclusions come from the same per-port
supplier. The statement also permits an empty family of cusp ports. -/
theorem PersistentCuspExterior.exists_uniform_cusp_postMetric_hessian_tolerance
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ}
    {C : PersistentHyperbolicCores F K} (E : PersistentCuspExterior C)
    (d : ∀ p : Σ i : Fin C.count, Fin (E.truncation i).count,
      SmoothTwoSidedCollar torusModel (𝓡 3)
        (fun s => (E.truncation p.1).cuspMap p.2 (s, halfZero)))
    (heq : ∀ (p : Σ i : Fin C.count, Fin (E.truncation i).count)
      (q : Torus × symmetricOpenInterval (d p).radius) (hq : 0 ≤ q.2.val),
      (d p).toFun q = (E.truncation p.1).cuspMap p.2 (q.1, halfPoint q.2.val hq))
    (R : ℝ) (hR : 0 < R) :
    ∃ δ : (Σ i : Fin C.count, Fin (E.truncation i).count) → ℝ,
      ∃ r ε : ℝ, 0 < r ∧ r ≤ R ∧ 0 < ε ∧ ε ≤ 1 / 2 ∧
      ∀ p : Σ i : Fin C.count, Fin (E.truncation i).count,
        0 < δ p ∧ δ p < (d p).radius ∧ 2 * r < δ p ∧
        let B : Set (d p).neighborhood :=
          {q | |collarHeight (C.model p.1) (E.truncation p.1) p.2 (d p) q| ≤ δ p}
        IsCompact B ∧
        {q : (d p).neighborhood |
          |collarHeight (C.model p.1) (E.truncation p.1) p.2 (d p) q| ≤ r / 2} ⊆ B ∧
        ∀ (t : ℝ) (ht : E.start ≤ t)
          (_hU : ((d p).neighborhood : Set (C.model p.1).Carrier) ⊆ C.domain p.1 t),
          C.accuracy t < ε →
          ∀ (ρ : C^∞⟮𝓡 3, (postStage F.observation t).Carrier; ℝ⟯)
            (x : (d p).neighborhood), x ∈ B →
            (x : (C.model p.1).Carrier) ∈ riemannianBallOf
              (C.model p.1).metric (C.model p.1).basepoint (C.accuracy t)⁻¹ →
            (collarRho (C.model p.1) (E.truncation p.1) p.2 (d p) =ᶠ[nhds x]
              fun y : (d p).neighborhood =>
                ρ (C.map p.1 t (E.after_cores.trans ht) y)) →
            ∀ V : TangentSpace (𝓡 3) (C.map p.1 t (E.after_cores.trans ht) x), V ≠ 0 →
              0 < hessFun (postMetric F.observation t) ρ
                (C.map p.1 t (E.after_cores.trans ht) x) V V := by
  classical
  let Port := Σ i : Fin C.count, Fin (E.truncation i).count
  choose δ η hdata using fun p : Port =>
    E.exists_compact_cusp_postMetric_hessian_tolerance p.1 p.2 (d p) (heq p)
  have hδ (p : Port) : 0 < δ p := (hdata p).1
  have hη (p : Port) : 0 < η p := (hdata p).2.2.1
  have hδnear : ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ p : Port, r < δ p / 2 := by
    apply Filter.eventually_all.mpr
    intro p
    exact (eventually_lt_nhds (half_pos (hδ p))).filter_mono nhdsWithin_le_nhds
  have hRnear : ∀ᶠ r : ℝ in 𝓝[>] 0, r < R :=
    (eventually_lt_nhds hR).filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := eventually_mem_nhdsWithin
  obtain ⟨r, hr, hrR, hrδ⟩ := (hpos.and (hRnear.and hδnear)).exists
  have hηnear : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ p : Port, ε < η p := by
    apply Filter.eventually_all.mpr
    intro p
    exact (eventually_lt_nhds (hη p)).filter_mono nhdsWithin_le_nhds
  have hhalf : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < 1 / 2 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 / 2 by norm_num)).filter_mono
      nhdsWithin_le_nhds
  obtain ⟨ε, hεpos, hεhalf, hεη⟩ := (hpos.and (hhalf.and hηnear)).exists
  refine ⟨δ, r, ε, hr, hrR.le, hεpos, hεhalf.le, ?_⟩
  intro p
  obtain ⟨hδpos, hδd, _, _, hB, hsign⟩ := hdata p
  have hrband : 2 * r < δ p := by linarith [hrδ p]
  refine ⟨hδpos, hδd, hrband, hB, ?_, ?_⟩
  · intro q hq
    change |collarHeight (C.model p.1) (E.truncation p.1) p.2 (d p) q| ≤ δ p
    change |collarHeight (C.model p.1) (E.truncation p.1) p.2 (d p) q| ≤ r / 2 at hq
    linarith
  · intro t ht hU haccuracy ρ x hx hxball hρ V hV
    exact hsign t ht hU (haccuracy.trans (hεη p)) ρ x hx hxball hρ V hV

end GC.LongTime

open Filter
open scoped Topology

namespace GC.LongTime

universe u

/-- The original persistent cusp exterior has a fixed positive profile width
and a common late-time threshold. Every resulting profile has positive full
Hessian in the original physical metric on its entire nonnegative strip.
The same exterior is its zero sublevel, and its positive domain has compact
closure. No Hessian sign or replacement metric is assumed. -/
theorem PersistentCuspExterior.exists_eventual_convex_profiles
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ}
    (C : PersistentHyperbolicCores F K) (E : PersistentCuspExterior C) (tmin : ℝ) :
    ∃ a : ℝ, 0 < a ∧ ∃ T : ℝ, ∃ hstart : E.start ≤ T,
      tmin ≤ T ∧ 1 ≤ T ∧ ∀ (t : ℝ) (ht : T ≤ t),
        ∃ ρ : (postStage F.observation t).Carrier → ℝ,
          ContMDiff (𝓡 3) 𝓘(ℝ) ∞ ρ ∧
          E.region t = {x | ρ x ≤ 0} ∧
          IsCompact (closure {x | ρ x < a}) ∧
          (∀ (i : Fin C.count) (j : Fin (E.truncation i).count) (s : Torus),
            ρ (C.map i t (E.after_cores.trans (hstart.trans ht))
              ((E.truncation i).cuspMap j (s, halfZero))) = 0) ∧
          ∀ x, 0 ≤ ρ x → ρ x < a →
            mfderiv (𝓡 3) 𝓘(ℝ) ρ x ≠ 0 ∧
            ∀ V : TangentSpace (𝓡 3) x, V ≠ 0 →
              0 < hessFun (postMetric F.observation t) ρ x V V := by
  classical
  obtain ⟨d, hd, R, hR, _, B, _, _, hneigh, hprofiles⟩ :=
    PersistentCuspExterior.exists_eventual_collar_profiles C E
  obtain ⟨δ, r, ε, hr, hrR, hε, _, huniform⟩ :=
    E.exists_uniform_cusp_postMetric_hessian_tolerance d hd R hR
  obtain ⟨T, hstart, htmin, h1, hlate⟩ := hprofiles tmin 2 ε hε
  let a : ℝ := (Real.exp (r / 2) - 1) / 2
  have ha : 0 < a := by
    have hexp := Real.one_lt_exp_iff.mpr (half_pos hr)
    dsimp only [a]
    linarith
  refine ⟨a, ha, T, hstart, htmin, h1, ?_⟩
  intro t ht
  obtain ⟨haccuracy, _, hball, hdomain, _, Φ, _, _, _, _, _, _,
    _, _, _, _, hprofile⟩ := hlate t ht
  obtain ⟨_, _, ρ, hρ, hregion, _, _, hcentral, _, hstrip⟩ := hprofile r hr hrR
  refine ⟨ρ, hρ, hregion, isClosed_closure.isCompact, ?_, ?_⟩
  · intro i j s
    let p : Σ i : Fin C.count, Fin (E.truncation i).count := ⟨i, j⟩
    let z : Torus × symmetricOpenInterval (d p).radius :=
      (s, ⟨0, neg_lt_zero.mpr (d p).radius_pos, (d p).radius_pos⟩)
    have hz : (d p).toPartialDiffeomorph (s, (0 : ℝ)) =
        (E.truncation i).cuspMap j (s, halfZero) := by
      calc
        _ = (d p).toFun z := (d p).toPartialDiffeomorph_apply z
        _ = _ := hd p z le_rfl
    have hzero := hcentral p s 0 (by constructor <;> linarith)
    rw [hz] at hzero
    simpa only [neg_zero, Real.exp_zero, sub_self] using hzero
  intro x hx hxa
  obtain ⟨hregular, p, _, _, z, hz, hmap, hmodel⟩ := hstrip x hx hxa
  refine ⟨hregular, ?_⟩
  obtain ⟨⟨s, h⟩, hh, hz⟩ := hz
  obtain ⟨_, hδd, hrδ, _, hcentralBand, hsign⟩ := huniform p
  have hhradius : h ∈ Ioo (-(d p).radius) (d p).radius := by
    constructor <;> linarith [hh.2.1, hh.2.2]
  let q : (d p).neighborhood := (d p).toDiffeomorph (s, ⟨h, hhradius⟩)
  have hqheight : collarHeight (C.model p.1) (E.truncation p.1) p.2 (d p) q = h := by
    simp only [collarHeight, q, Diffeomorph.symm_apply_apply]
  have hqimage : (d p).toPartialDiffeomorph (s, h) =
      (q : (C.model p.1).Carrier) :=
    (d p).toPartialDiffeomorph_apply (s, ⟨h, hhradius⟩)
  have hqz : (q : (C.model p.1).Carrier) = z := hqimage.symm.trans hz
  have hqband := hcentralBand (show q ∈ {y : (d p).neighborhood |
      |collarHeight (C.model p.1) (E.truncation p.1) p.2 (d p) y| ≤ r / 2} from by
    rw [mem_ofPred_eq, hqheight, abs_le]
    constructor <;> linarith [hh.2.1, hh.2.2])
  have hU : ((d p).neighborhood : Set (C.model p.1).Carrier) ⊆ C.domain p.1 t :=
    (hneigh p).trans (hdomain p.1)
  have hqball := hball p.1 (hneigh p q.property)
  have hsub : Tendsto (Subtype.val : (d p).neighborhood → (C.model p.1).Carrier)
      (𝓝 q) (𝓝 z) := by
    rw [← hqz]
    exact continuous_subtype_val.continuousAt.tendsto
  have hmodelq := hmodel.comp_tendsto hsub
  have hσ : collarRho (C.model p.1) (E.truncation p.1) p.2 (d p) =ᶠ[𝓝 q]
      fun y : (d p).neighborhood =>
        ρ (C.map p.1 t (E.after_cores.trans (hstart.trans ht)) y) := by
    filter_upwards [hmodelq] with y hy
    dsimp only [Function.comp_def] at hy
    rw [(d p).toPartialDiffeomorph_symm_apply y] at hy
    exact hy.symm
  have hphysical := hsign t (hstart.trans ht) hU haccuracy ⟨ρ, hρ⟩ q hqband hqball hσ
  rw [← hmap, ← hqz]
  exact hphysical

end GC.LongTime
