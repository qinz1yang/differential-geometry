import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.FiniteTraceEnergy
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.Algebra

/-!
# S-CH11-PORT-B1 port of `Perelman.LGeometry.Index.FiniteJointRayTrace` (`PortC11P`)

Source: donor
`DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/LGeometry/Index/FiniteJointRayTrace.lean`
of the chapter-11 branch (ch11 HEAD a73e4bdbfd).  The donor file does not elaborate against this
tree (same lakefile, Lean v4.35.0-rc3, same Mathlib).  Three elaboration-level repairs, all in the
proof of `lVelocity_parameter_ray_eq_mfderiv`:
* line 46: `simpa only [one_smul, id_eq]` (the term carries `fun y => id y • ξ`).
* lines 50-51: `simpa only [zero_smul] using ...` becomes `rw [zero_smul]; exact ...` (the point
  `0 • ξ` occurs in the type of the derivative argument, so `simp` cannot rewrite it).
* lines 52-53: `hcomp` is given the explicit type `HasMFDerivAt ... (fun u => f (u • ξ)) 0 _`
  so that `rw [hcomp.mfderiv]` finds the syntactic `mfderiv (fun u => f (u • ξ)) 0` (the
  composite `f ∘ fun u => u • ξ` is defeq but not syntactically equal).
No statement, definition or proof idea is altered.  The module
`Perelman.LGeometry.Index.FiniteJointRayTrace` is a shim re-exporting this file.
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Set Bundle Filter MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open scoped _root_.Manifold ContDiff _root_.Topology BigOperators

universe uM uE uH uP

/-- The actual velocity of a parameter ray is the full parameter derivative
applied to its direction. The equality has an explicit model-space codomain. -/
theorem lVelocity_parameter_ray_eq_mfderiv
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (f : P → M) (hf : MDifferentiableAt 𝓘(ℝ, P) I f 0) (ξ : P) :
    (lVelocity (I := I) (fun u : ℝ => f (u • ξ)) 0 : E) =
      (mfderiv 𝓘(ℝ, P) I f 0 ξ : E) := by
  have hline : HasDerivAt (fun u : ℝ => u • ξ) ξ 0 := by
    simpa only [one_smul, id_eq] using (hasDerivAt_id (0 : ℝ)).smul_const ξ
  unfold lVelocity
  have hendAt : HasMFDerivAt 𝓘(ℝ, P) I f ((0 : ℝ) • ξ)
      (mfderiv 𝓘(ℝ, P) I f 0) := by
    rw [zero_smul]
    exact hf.hasMFDerivAt
  have hcomp : HasMFDerivAt 𝓘(ℝ, ℝ) I (fun u : ℝ => f (u • ξ)) 0 _ :=
    hendAt.comp 0 hline.hasFDerivAt.hasMFDerivAt
  rw [hcomp.mfderiv]
  change mfderiv 𝓘(ℝ, P) I f 0
    ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) ξ) 1) = _
  simp

/-- The existing adapted-frame trace energy received by the rays of one given
joint family. A list of directions suffices; a parameter basis is a direct
specialization. No replacement family or vanishing endpoint velocity is used. -/
theorem sum_lRegularizedIndex_parameter_rays_eq_energy
    {n : ℕ} {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Fin (n + 1) → Type uM} [∀ i, TopologicalSpace (M i)]
    [∀ i, ChartedSpace H (M i)] [∀ i, IsManifold I ∞ (M i)] [∀ i, T2Space (M i)]
    {D : Fin (n + 1) → RealTimeInterval}
    {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (S : (i : Fin (n + 1)) → SolutionOn (I := I) (M := M i) (D i))
    (hS : ∀ i, IsSolutionOn (S i)) (T : ℝ)
    (alpha : (i : Fin (n + 1)) → ℝ → M i)
    (s : Fin (n + 2) → ℝ) (hs : Monotone s) (ha : 0 < s 0)
    (hav : s 0 < s (Fin.last (n + 1)))
    (Pframe : (i : Fin (n + 1)) → Fin (Module.finrank ℝ E) →
      ∀ t, TangentSpace I (alpha i t))
    (hgeo : ∀ i, IsLRegularizedGeodesicOn (S i) T (alpha i)
      (Ioo (s i.castSucc) (s i.succ)))
    (hLag : ∀ i, ContinuousOn (lRegularizedLagrangian (S i) T (alpha i))
      (Icc (s i.castSucc) (s i.succ)))
    (hHam : ∀ i, IntervalIntegrable (lHamSq (S i) T (alpha i)) volume
      (s i.castSucc) (s i.succ))
    (hreg : ∀ i, ∀ t ∈ Icc (s i.castSucc) (s i.succ), T - t ^ 2 ∈ (D i).regular)
    (halpha : ∀ i, ∀ t ∈ Icc (s i.castSucc) (s i.succ),
      MDifferentiableAt 𝓘(ℝ, ℝ) I (alpha i) t)
    (hP : ∀ i k t, t ∈ Icc (s i.castSucc) (s i.succ) →
      DifferentiableAt ℝ (chartRepAt (I := I) (alpha i) (Pframe i k) t) t)
    (hDP : ∀ i k, IsLAdapted (S i) T (alpha i) (Pframe i k)
      (Icc (s i.castSucc) (s i.succ)))
    (hON : ∀ i k l,
      ((S i).base.metric (T - (s i.succ) ^ 2)).inner (alpha i (s i.succ))
        (Pframe i k (s i.succ)) (Pframe i l (s i.succ)) = if k = l then 1 else 0)
    (hindexInt : ∀ i k, IntervalIntegrable
      (lRegularizedIndexIntegrand (S i) T (alpha i)
        (fun t => ((t - s 0) / (s (Fin.last (n + 1)) - s 0)) • Pframe i k t)
        (fun t => ((t - s 0) / (s (Fin.last (n + 1)) - s 0)) • Pframe i k t))
      volume (s i.castSucc) (s i.succ))
    (hscalar : ∀ i : Fin n,
      (S i.castSucc).scalar (T - (s i.castSucc.succ) ^ 2)
          (alpha i.castSucc (s i.castSucc.succ)) =
        (S i.succ).scalar (T - (s i.succ.castSucc) ^ 2)
          (alpha i.succ (s i.succ.castSucc)))
    (hlag : ∀ i : Fin n,
      lRegularizedLagrangian (S i.castSucc) T (alpha i.castSucc) (s i.castSucc.succ) =
        lRegularizedLagrangian (S i.succ) T (alpha i.succ) (s i.succ.castSucc))
    (f : (i : Fin (n + 1)) → P × ℝ → M i)
    (hf : ∀ i, ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) I (8 : ℕ) (f i))
    (directions : Fin (Module.finrank ℝ E) → P)
    (hcenter : ∀ i t, t ∈ Icc (s i.castSucc) (s i.succ) →
      (fun r => f i (0, r)) =ᶠ[𝓝 t] alpha i)
    (hfield : ∀ i k t, t ∈ Icc (s i.castSucc) (s i.succ) →
      Filter.EventuallyEq (β := E) (𝓝 t)
        (fun r => (mfderiv 𝓘(ℝ, P) I (fun z => f i (z, r)) 0 (directions k) : E))
        (fun r => (((r - s 0) / (s (Fin.last (n + 1)) - s 0)) • Pframe i k r : E))) :
    let a := s 0;
    let v := s (Fin.last (n + 1));
    2 * (∑ i : Fin (n + 1), ∑ k : Fin (Module.finrank ℝ E),
      lRegularizedIndex (S i) T (fun r => f i (0, r))
        (fun r => lVelocity (I := I) (fun u : ℝ => f i (u • directions k, r)) 0)
        (fun r => lVelocity (I := I) (fun u : ℝ => f i (u • directions k, r)) 0)
        (s i.castSucc) (s i.succ)) =
      (Module.finrank ℝ E : ℝ) / (v - a) -
        v * (S (Fin.last n)).scalar (T - v ^ 2) (alpha (Fin.last n) v) -
        (∑ i : Fin (n + 1), ∫ t in (s i.castSucc)..(s i.succ),
          (1 - a ^ 2 / t ^ 2) * lRegularizedLagrangian (S i) T (alpha i) t) /
            (2 * (v - a) ^ 2) +
        ((S (Fin.last n)).base.metric (T - v ^ 2)).inner (alpha (Fin.last n) v)
          (lVelocity (I := I) (alpha (Fin.last n)) v)
          (lVelocity (I := I) (alpha (Fin.last n)) v) / (4 * v) := by
  classical
  let a := s 0
  let v := s (Fin.last (n + 1))
  let Y (i : Fin (n + 1)) (k : Fin (Module.finrank ℝ E)) (r : ℝ) :
      TangentSpace I (alpha i r) := ((r - a) / (v - a)) • Pframe i k r
  have htrace := sum_lRegularizedIndex_trace_linear_cutoff_eq_energy S hS T alpha s
    hs ha hav Pframe hgeo hLag hHam hreg halpha hP hDP hON hindexInt hscalar hlag
  have hslice (i : Fin (n + 1)) (r : ℝ) :
      MDifferentiableAt 𝓘(ℝ, P) I (fun z => f i (z, r)) 0 :=
    (((hf i).comp (contMDiff_id.prodMk contMDiff_const)).contMDiffAt).mdifferentiableAt
      (by norm_num)
  have hray (i : Fin (n + 1)) (ξ : P) (r : ℝ) :
      (lVelocity (I := I) (fun u : ℝ => f i (u • ξ, r)) 0 : E) =
        (mfderiv 𝓘(ℝ, P) I (fun z => f i (z, r)) 0 ξ : E) :=
    lVelocity_parameter_ray_eq_mfderiv (fun z => f i (z, r)) (hslice i r) ξ
  have hfieldRay (i : Fin (n + 1)) (k : Fin (Module.finrank ℝ E))
      (t : ℝ) (ht : t ∈ Icc (s i.castSucc) (s i.succ)) :
      Filter.EventuallyEq (β := E) (𝓝 t)
        (fun r => (lVelocity (I := I) (fun u : ℝ => f i (u • directions k, r)) 0 : E))
        (fun r => (Y i k r : E)) := by
    filter_upwards [hfield i k t ht] with r hr
    exact (hray i (directions k) r).trans hr
  have heq :
      (∑ i : Fin (n + 1), ∑ k : Fin (Module.finrank ℝ E),
        lRegularizedIndex (S i) T (fun r => f i (0, r))
          (fun r => lVelocity (I := I) (fun u : ℝ => f i (u • directions k, r)) 0)
          (fun r => lVelocity (I := I) (fun u : ℝ => f i (u • directions k, r)) 0)
          (s i.castSucc) (s i.succ)) =
        ∑ i : Fin (n + 1), ∑ k : Fin (Module.finrank ℝ E),
          lRegularizedIndex (S i) T (alpha i) (Y i k) (Y i k)
            (s i.castSucc) (s i.succ) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    have hab : s i.castSucc ≤ s i.succ := hs i.castSucc_le_succ
    apply lRegularizedIndex_congr_of_eventuallyEq
    · intro t ht
      rw [uIoo_of_le hab] at ht
      exact hcenter i t (Ioo_subset_Icc_self ht)
    · intro t ht
      rw [uIoo_of_le hab] at ht
      exact hfieldRay i k t (Ioo_subset_Icc_self ht)
    · intro t ht
      rw [uIoo_of_le hab] at ht
      exact hfieldRay i k t (Ioo_subset_Icc_self ht)
  rw [heq]
  exact htrace

end DifferentialGeometry.PDE.RicciFlow.Perelman
