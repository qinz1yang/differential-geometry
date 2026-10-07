import DifferentialGeometry.Geometry.Comparison.Variation.Field.FiniteJointFrames
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.FiniteTraceEnergy
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.Algebra
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.CovariantDerivativeAlong

/-!
# S-CH11-FIX4 port of `Perelman.LGeometry.Index.FiniteJointTrace` (`PortC11P`)

Source: donor `DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/LGeometry/Index/`
`FiniteJointTrace.lean` of the chapter-11 branch (ch11 HEAD a73e4bdbfd).  Verbatim it does
not elaborate against this tree (3 errors, all in the proof of
`exists_compatible_joint_variation_with_index_trace_energy`).
Three elaboration-level repairs (`TangentSpace I _` vs `E` and let-variable unfolding):
* `hmatch`: `simpa only [..] using congrArg ..` becomes `have h := congrArg ..;
  simp only [..] at h ⊢; exact h` (the simp-normal forms agree, the carrier types
  `TangentSpace I (Phi i _)` and `E` only agree by `exact`).
* `hfirst`: a closing `rfl` after the `simp only` (the residual `0 = 0` lives in `TangentSpace`
  with non-syntactic instances).
* last bullet of `refine`: the `v` abbreviation is added to the `simpa only` set so
  `div_self` sees `(s (Fin.last _) - a) / (v - a)`.
No statement, definition or proof idea is altered.  The module
`Perelman.LGeometry.Index.FiniteJointTrace` is a shim re-exporting this file.
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Set Bundle Filter MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.Exponential
open scoped _root_.Manifold ContDiff _root_.Topology BigOperators

universe uM uE uH

/-- One compatible joint variation for the linear-cutoff adapted frames on the
same finite Ricci-flow pieces. The index trace is computed from the actual
parameter derivatives of this family. Its final endpoint has the exponential
germ of the physical final metric, and the energy identity retains the final
velocity. -/
theorem exists_compatible_joint_variation_with_index_trace_energy
    {n : ℕ} {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Fin (n + 1) → Type uM} [∀ i, TopologicalSpace (M i)]
    [∀ i, ChartedSpace H (M i)] [∀ i, IsManifold I ∞ (M i)] [∀ i, T2Space (M i)]
    {D : Fin (n + 1) → RealTimeInterval}
    (S : (i : Fin (n + 1)) → SolutionOn (I := I) (M := M i) (D i))
    (hS : ∀ i, IsSolutionOn (S i)) (T : ℝ)
    (alpha : (i : Fin (n + 1)) → ℝ → M i)
    (s : Fin (n + 2) → ℝ) (hs : StrictMono s) (ha : 0 < s 0)
    (P : (i : Fin (n + 1)) → Fin (Module.finrank ℝ E) →
      ∀ t, TangentSpace I (alpha i t))
    (Omega : Fin (n + 1) → Set ℝ) (hOmega : ∀ i, IsOpen (Omega i))
    (hseg : ∀ i, Icc (s i.castSucc) (s i.succ) ⊆ Omega i)
    (halphaC8 : ∀ i, ContMDiffOn 𝓘(ℝ, ℝ) I (8 : ℕ) (alpha i) (Omega i))
    (hPbundleC8 : ∀ i k, ContMDiffOn 𝓘(ℝ, ℝ) I.tangent (8 : ℕ)
      (fun t => (⟨alpha i t, P i k t⟩ : TangentBundle I (M i))) (Omega i))
    (Phi : (i : Fin n) → M i.castSucc → M i.succ)
    (U : (i : Fin n) → Set (M i.castSucc)) (hUopen : ∀ i, IsOpen (U i))
    (hPhi : ∀ i, ContMDiffOn I I (8 : ℕ) (Phi i) (U i))
    (hsource : ∀ i, alpha i.castSucc (s i.castSucc.succ) ∈ U i)
    (hpoint : ∀ i, Phi i (alpha i.castSucc (s i.castSucc.succ)) =
      alpha i.succ (s i.succ.castSucc))
    (hframe : ∀ i k,
      (mfderiv I I (Phi i) (alpha i.castSucc (s i.castSucc.succ))
        (P i.castSucc k (s i.castSucc.succ)) : E) = P i.succ k (s i.succ.castSucc))
    (hgeo : ∀ i, IsLRegularizedGeodesicOn (S i) T (alpha i)
      (Ioo (s i.castSucc) (s i.succ)))
    (hLag : ∀ i, ContinuousOn (lRegularizedLagrangian (S i) T (alpha i))
      (Icc (s i.castSucc) (s i.succ)))
    (hHam : ∀ i, IntervalIntegrable (lHamSq (S i) T (alpha i)) volume
      (s i.castSucc) (s i.succ))
    (hreg : ∀ i, ∀ t ∈ Icc (s i.castSucc) (s i.succ), T - t ^ 2 ∈ (D i).regular)
    (hDP : ∀ i k, IsLAdapted (S i) T (alpha i) (P i k)
      (Icc (s i.castSucc) (s i.succ)))
    (hON : ∀ i k l,
      ((S i).base.metric (T - (s i.succ) ^ 2)).inner (alpha i (s i.succ))
        (P i k (s i.succ)) (P i l (s i.succ)) = if k = l then 1 else 0)
    (hindexInt : ∀ i k, IntervalIntegrable
      (lRegularizedIndexIntegrand (S i) T (alpha i)
        (fun t => ((t - s 0) / (s (Fin.last (n + 1)) - s 0)) • P i k t)
        (fun t => ((t - s 0) / (s (Fin.last (n + 1)) - s 0)) • P i k t))
      volume (s i.castSucc) (s i.succ))
    (hscalar : ∀ i : Fin n,
      (S i.castSucc).scalar (T - (s i.castSucc.succ) ^ 2)
          (alpha i.castSucc (s i.castSucc.succ)) =
        (S i.succ).scalar (T - (s i.succ.castSucc) ^ 2)
          (alpha i.succ (s i.succ.castSucc)))
    (hlag : ∀ i : Fin n,
      lRegularizedLagrangian (S i.castSucc) T (alpha i.castSucc) (s i.castSucc.succ) =
        lRegularizedLagrangian (S i.succ) T (alpha i.succ) (s i.succ.castSucc)) :
    let a := s 0;
    let v := s (Fin.last (n + 1));
    ∃ f : (i : Fin (n + 1)) → (Fin (Module.finrank ℝ E) → ℝ) × ℝ → M i,
      (∀ i, ContMDiff (𝓘(ℝ, Fin (Module.finrank ℝ E) → ℝ).prod 𝓘(ℝ, ℝ))
        I (8 : ℕ) (f i)) ∧
      (∀ i t, t ∈ Icc (s i.castSucc) (s i.succ) →
        (fun r => f i (0, r)) =ᶠ[𝓝 t] alpha i) ∧
      (∀ i k t, t ∈ Icc (s i.castSucc) (s i.succ) →
        Filter.EventuallyEq (β := E) (𝓝 t)
          (fun r => (mfderiv 𝓘(ℝ, Fin (Module.finrank ℝ E) → ℝ) I
            (fun z => f i (z, r)) 0 (Pi.single k 1) : E))
          (fun r => (((r - a) / (v - a)) • P i k r : E))) ∧
      (∀ z, f 0 (z, a) = alpha 0 a) ∧
      (∀ z i, f i.castSucc (z, s i.castSucc.succ) ∈ U i ∧
        Phi i (f i.castSucc (z, s i.castSucc.succ)) =
          f i.succ (z, s i.succ.castSucc)) ∧
      ((fun z => f (Fin.last n) (z, v)) =ᶠ[𝓝 (0 : Fin (Module.finrank ℝ E) → ℝ)]
        (fun z => expMap (I := I) ((S (Fin.last n)).base.metric (T - v ^ 2))
          (alpha (Fin.last n) v) (∑ k, z k • P (Fin.last n) k v))) ∧
      2 * (∑ i : Fin (n + 1), ∑ k : Fin (Module.finrank ℝ E),
        lRegularizedIndex (S i) T (fun r => f i (0, r))
          (fun r => mfderiv 𝓘(ℝ, Fin (Module.finrank ℝ E) → ℝ) I
            (fun z => f i (z, r)) 0 (Pi.single k 1))
          (fun r => mfderiv 𝓘(ℝ, Fin (Module.finrank ℝ E) → ℝ) I
            (fun z => f i (z, r)) 0 (Pi.single k 1))
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
  let chi : ℝ → ℝ := fun t => (t - a) / (v - a)
  let lower (i : Fin (n + 1)) := s i.castSucc
  let upper (i : Fin (n + 1)) := s i.succ
  let g (i : Fin (n + 1)) := (S i).base.metric (T - (upper i) ^ 2)
  let Y (i : Fin (n + 1)) (k : Fin (Module.finrank ℝ E)) (t : ℝ) :
      TangentSpace I (alpha i t) := chi t • P i k t
  have hab (i : Fin (n + 1)) : lower i < upper i := hs i.castSucc_lt_succ
  have hav : a < v := hs (by change 0 < n + 1; exact Nat.succ_pos n)
  have hchi : ContDiff ℝ (8 : ℕ) chi :=
    (contDiff_id.sub contDiff_const).div_const (v - a)
  have hY (i : Fin (n + 1)) (k : Fin (Module.finrank ℝ E)) :
      ContMDiffOn 𝓘(ℝ, ℝ) I.tangent (8 : ℕ)
        (fun t => (⟨alpha i t, Y i k t⟩ : TangentBundle I (M i))) (Omega i) :=
    hchi.contMDiff.contMDiffOn.smul_bundle (hPbundleC8 i k)
  have hmatch (i : Fin n) (k : Fin (Module.finrank ℝ E)) :
      (mfderiv I I (Phi i) (alpha i.castSucc (upper i.castSucc))
        (Y i.castSucc k (upper i.castSucc)) : E) = Y i.succ k (lower i.succ) := by
    have h := congrArg (fun Z : E => chi (s i.castSucc.succ) • Z) (hframe i k)
    simp only [Y, lower, upper, map_smul, Fin.castSucc_succ] at h ⊢
    exact h
  have hfirst (k : Fin (Module.finrank ℝ E)) : Y 0 k (lower 0) = 0 := by
    simp only [Y, chi, lower, a, Fin.castSucc_zero, sub_self, zero_div, zero_smul]
    rfl
  obtain ⟨f, hf, hcenter, hfield, hfix, hjoin, hend⟩ :=
    exists_compatible_joint_variation_of_fields g alpha Y lower upper hab Omega hOmega hseg
      halphaC8 hY Phi U hUopen hPhi hsource hpoint hmatch hfirst
  have halpha (i : Fin (n + 1)) (t : ℝ) (ht : t ∈ Icc (s i.castSucc) (s i.succ)) :
      MDifferentiableAt 𝓘(ℝ, ℝ) I (alpha i) t :=
    ((halphaC8 i).contMDiffAt ((hOmega i).mem_nhds (hseg i ht))).mdifferentiableAt
      (by norm_num)
  have hPdiff (i : Fin (n + 1)) (k : Fin (Module.finrank ℝ E))
      (t : ℝ) (ht : t ∈ Icc (s i.castSucc) (s i.succ)) :
      DifferentiableAt ℝ (chartRepAt (I := I) (alpha i) (P i k) t) t :=
    differentiableAt_chartRepAt_of_contMDiffAt_two
      (((hPbundleC8 i k).contMDiffAt ((hOmega i).mem_nhds (hseg i ht))).of_le
        (by norm_num : (2 : WithTop ℕ∞) ≤ (8 : WithTop ℕ∞)))
  have htrace := sum_lRegularizedIndex_trace_linear_cutoff_eq_energy S hS T alpha s
    hs.monotone ha hav P hgeo hLag hHam hreg halpha hPdiff hDP hON hindexInt hscalar hlag
  refine ⟨f, hf, hcenter, hfield, hfix, hjoin, ?_, ?_⟩
  · simpa only [g, upper, Y, chi, v, Fin.succ_last, div_self (sub_pos.mpr hav).ne',
      one_smul] using hend
  · have heq :
        (∑ i : Fin (n + 1), ∑ k : Fin (Module.finrank ℝ E),
          lRegularizedIndex (S i) T (fun r => f i (0, r))
            (fun r => mfderiv 𝓘(ℝ, Fin (Module.finrank ℝ E) → ℝ) I
              (fun z => f i (z, r)) 0 (Pi.single k 1))
            (fun r => mfderiv 𝓘(ℝ, Fin (Module.finrank ℝ E) → ℝ) I
              (fun z => f i (z, r)) 0 (Pi.single k 1))
            (s i.castSucc) (s i.succ)) =
          ∑ i : Fin (n + 1), ∑ k : Fin (Module.finrank ℝ E),
            lRegularizedIndex (S i) T (alpha i) (Y i k) (Y i k)
              (s i.castSucc) (s i.succ) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      apply lRegularizedIndex_congr_of_eventuallyEq
      · intro t ht
        rw [uIoo_of_le (hab i).le] at ht
        exact hcenter i t (Ioo_subset_Icc_self ht)
      · intro t ht
        rw [uIoo_of_le (hab i).le] at ht
        exact hfield i k t (Ioo_subset_Icc_self ht)
      · intro t ht
        rw [uIoo_of_le (hab i).le] at ht
        exact hfield i k t (Ioo_subset_Icc_self ht)
    rw [heq]
    exact htrace

end DifferentialGeometry.PDE.RicciFlow.Perelman
