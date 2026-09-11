import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifference.LoweredCoefficient
import DifferentialGeometry.Geometry.Metric.Convergence.Coordinates.Control
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Self
import DifferentialGeometry.Geometry.Metric.Convergence.Coordinates.GoodFrame
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Arity
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence
import DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.Riemannian
import DifferentialGeometry.Geometry.Coordinates.Connection.Christoffel

set_option autoImplicit false

open Bundle Manifold Set Filter DifferentialGeometry
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open scoped Manifold ContDiff BigOperators Topology

noncomputable section

namespace DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [T2Space M]
  {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

omit [DecidableEq Idx] in
private theorem lowered_component_contraction
    (G g : SmoothRiemannianMetric I M)
    (frame : Idx → (x : M) → TangentSpace I x) {u : Set M}
    (hframe : IsLocalFrameOn I E 1 frame u) (hu : IsOpen u)
    {x : M} (hx : x ∈ u) (idx : Fin 3 → Idx) :
    frameComp0S (metricLoweredConnectionDifferenceField G g) frame x
        (fun i => idx (Equiv.swap (0 : Fin 3) 1 i)) =
      contrTail
        (fun m : Fin 3 → Idx =>
          christoffelSymbolInFrame (leviCivitaConnectionOfMetric g) frame hframe x
              (m 0) (m 1) (m 2) -
            christoffelSymbolInFrame (leviCivitaConnectionOfMetric G) frame hframe x
              (m 0) (m 1) (m 2))
        (frameComp0S (metricTensorField G) frame x) idx := by
  classical
  have hmd := ((hframe.contMDiffOn (idx 1)).contMDiffAt (hu.mem_nhds hx)).mdifferentiableAt
    (show (1 : WithTop ℕ∞) ≠ 0 by simp)
  rw [frameComp0S_apply]
  change G.inner x (PDE.DeTurck.connectionDifference g G x
    (frame (idx (Equiv.swap (0 : Fin 3) 1 0)) x)
    (frame (idx (Equiv.swap (0 : Fin 3) 1 1)) x))
    (frame (idx (Equiv.swap (0 : Fin 3) 1 2)) x) = _
  simp only [Equiv.swap_apply_left, Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne (by decide : (2 : Fin 3) ≠ 0) (by decide : (2 : Fin 3) ≠ 1)]
  change G.inner x
    ((CovariantDerivative.difference (leviCivitaConnectionOfMetric g)
      (leviCivitaConnectionOfMetric G) x (frame (idx 1) x)) (frame (idx 0) x))
    (frame (idx 2) x) = _
  rw [DifferentialGeometry.Tensor.Coordinates.christoffelSymbolDifference_expansion _ _ frame hframe hx,
    map_sum, sum_apply, contrTail_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [ContinuousLinearMap.map_smul, smul_apply, smul_eq_mul]
  rw [DifferentialGeometry.Tensor.Coordinates.christoffelSymbolDifferenceInFrame_eq_sub _ _ frame hframe
    (idx 0) (idx 1) d hmd]
  change _ * G.inner x (frame d x) (frame (idx 2) x) =
    _ * G.inner x (frame (idx 2) x) (frame d x)
  rw [G.symm]
  rfl

private theorem lowered_tower_norm_le
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e]
    (G g : SmoothRiemannianMetric I M) (basis : Module.Basis Idx ℝ E)
    {x : M} (hx : x ∈ e.baseSet)
    (hinv : MetricInverseInBasis G x
      ((e.isLocalFrameOn_localFrame_baseSet I 1 basis).toBasisAt hx)
      (identityInvMetric (Idx := Idx))) (m : ℕ) :
    Real.sqrt (normSq0S G x (3 + m)
      (iterCov G 3 (metricLoweredConnectionDifferenceField G g) m x)) ≤
    compL2 (iterCovCompU (I := I) (fun a y => e.localFrame basis a y)
      (fun y => christoffelSymbolInFrame (leviCivitaConnectionOfMetric G)
        (fun a z => e.localFrame basis a z)
        (e.isLocalFrameOn_localFrame_baseSet I 1 basis) y)
      (akCompField e g G basis) m x) *
    compL2 (frameComp0S (metricTensorField G) (fun a y => e.localFrame basis a y) x) := by
  let frame := fun a y => e.localFrame basis a y
  let hf := e.isLocalFrameOn_localFrame_baseSet I 1 basis
  let chr := fun y => christoffelSymbolInFrame (leviCivitaConnectionOfMetric G) frame hf y
  let F := frameComp0S (metricLoweredConnectionDifferenceField G g) frame
  let B := frameComp0S (metricTensorField G) frame
  let A := akCompField e g G basis
  have hcomp : ∀ y ∈ e.baseSet,
      (fun k : Fin 3 → Idx => F y (fun i => k (Equiv.swap (0 : Fin 3) 1 i))) =
      contrTail (A y) (B y) := by
    intro y hy
    funext k
    exact lowered_component_contraction G g frame hf e.open_baseSet hy k
  have hnorm : Real.sqrt (normSq0S G x (3 + m)
      (iterCov G 3 (metricLoweredConnectionDifferenceField G g) m x)) =
      compL2 (iterCovComp (I := I) frame chr (fun y => contrTail (A y) (B y)) m x) := by
    rw [← compL2_tower_eq G (metricLoweredConnectionDifferenceField G g)
      frame hf e.open_baseSet hx hinv m]
    change compL2 (iterCovComp (I := I) frame chr F m x) = _
    rw [← compL2_iterCovComp_compReindex (Equiv.swap (0 : Fin 3) 1) frame chr F m x,
      iterCovComp_congr_on e.open_baseSet frame chr hcomp m x hx]
  rw [hnorm]
  have hb := compL2_iterCovComp_contrTail_le e.open_baseSet frame chr
    (fun d => frame_e_mdiffOn e basis d)
    (fun d i j => lcChrist_e_mdiffOn e G basis d i j) m A B
    (fun k => akCompField_mdiffOn e g G basis k)
    (fun k => gCompField_mdiffOn e G basis k) hx
  have hzero : ∀ j, compL2 (iterCovComp (I := I) frame chr B (j + 1) x) = 0 := by
    intro j
    rw [compL2_tower_eq G (metricTensorField G) frame hf e.open_baseSet hx hinv (j + 1),
      ← metricCovDerivNorm_eq_iterCov G G (j + 1) (hf.toBasisAt hx) hinv,
      covNorm_self_succ]
  have hsum : (∑ c ∈ Finset.range (m + 1), (m.choose c : ℝ) *
      compL2 (iterCovCompU (I := I) frame chr A c x) *
      compL2 (iterCovComp (I := I) frame chr B (m - c) x)) =
      compL2 (iterCovCompU (I := I) frame chr A m x) * compL2 (B x) := by
    rw [Finset.sum_eq_single m]
    · simp only [Nat.choose_self, Nat.cast_one, one_mul]
      exact congrArg (fun a : ℕ => compL2 (iterCovCompU (I := I) frame chr A m x) *
        compL2 (iterCovComp (I := I) frame chr B a x)) (Nat.sub_self m)
    · intro c hc hcm
      have hpos : 0 < m - c := by
        have hc' := Finset.mem_range.mp hc
        omega
      obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
      rw [hj, hzero]
      simp
    · intro hm
      exact (hm (Finset.mem_range.mpr (Nat.lt_succ_self m))).elim
  rw [hsum] at hb
  exact hb

omit [DecidableEq Idx] in
private theorem continuousAt_compL2 {X : Type*} [TopologicalSpace X] {r : ℕ}
    {F : X → (Fin r → Idx) → ℝ} {x : X}
    (hF : ∀ k, ContinuousAt (fun y => F y k) x) :
    ContinuousAt (fun y => compL2 (F y)) x := by
  classical
  exact (show ContinuousAt (fun y => ∑ k, (F y k) ^ 2) x from
    tendsto_finsetSum Finset.univ (fun k _ => (hF k).pow 2)).sqrt

omit [CompleteSpace E] [BoundarylessManifold I M] [T2Space M] in
private theorem continuousAt_ginv_compL2
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e]
    (g : SmoothRiemannianMetric I M) (basis : Module.Basis Idx ℝ E)
    {x : M} (hx : x ∈ e.baseSet) :
    ContinuousAt (fun y => compL2 (ginvCompField e g basis y)) x := by
  have hmat : ContinuousAt (fun y => gramE e g basis y) x := by
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    have h := ((gCompField_mdiffOn e g basis ![i, j]).contMDiffAt
      (e.open_baseSet.mem_nhds hx)).continuousAt
    change ContinuousAt (fun y => g.inner y (e.localFrame basis i y)
      (e.localFrame basis j y)) x at h ⊢
    exact h
  have hinv : ContinuousAt Inv.inv (gramE e g basis x) := by
    apply continuousAt_matrix_inv
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (ne_of_gt (gramE_posDef e g basis hx).det_pos)
  have h := hinv.comp hmat
  apply continuousAt_compL2
  intro k
  exact ((continuousAt_pi.mp ((continuousAt_pi.mp h) (k 0))) (k 1))

omit [BoundarylessManifold I M] [DecidableEq Idx] in
private theorem continuousAt_metric_component_jet_norm
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e]
    (G g : SmoothRiemannianMetric I M) (basis : Module.Basis Idx ℝ E)
    {x : M} (hx : x ∈ e.baseSet) (j : ℕ) :
    ContinuousAt (fun y => compL2
      (iterCovComp (I := I) (fun a z => e.localFrame basis a z)
        (fun z => christoffelSymbolInFrame (leviCivitaConnectionOfMetric G)
          (fun a z' => e.localFrame basis a z')
          (e.isLocalFrameOn_localFrame_baseSet I 1 basis) z)
        (frameComp0S (metricTensorField g) (fun a z => e.localFrame basis a z)) j y)) x := by
  classical
  apply continuousAt_compL2
  intro k
  exact ((iterCovComp_contMDiffOn e.open_baseSet
    (fun a z => e.localFrame basis a z)
    (fun z => christoffelSymbolInFrame (leviCivitaConnectionOfMetric G)
      (fun a z' => e.localFrame basis a z')
      (e.isLocalFrameOn_localFrame_baseSet I 1 basis) z)
    (frameComp0S (metricTensorField g) (fun a z => e.localFrame basis a z))
    (fun d => frame_e_mdiffOn e basis d)
    (fun d i j' => lcChrist_e_mdiffOn e G basis d i j')
    (fun k' => gCompField_mdiffOn e g basis k') j k).contMDiffAt
    (e.open_baseSet.mem_nhds hx)).continuousAt

omit [BoundarylessManifold I M] in
private theorem component_tower_bound_at
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e]
    (G g : SmoothRiemannianMetric I M) (basis : Module.Basis Idx ℝ E)
    {x : M} (hx : x ∈ e.baseSet) (m : ℕ) (C0 B : ℝ)
    (hInv : compL2 (ginvCompField e g basis x) ≤ C0)
    (hJet : ∀ a, 1 ≤ a → a ≤ m + 1 →
      compL2 (iterCovComp (I := I) (fun d y => e.localFrame basis d y)
        (fun y => christoffelSymbolInFrame (leviCivitaConnectionOfMetric G)
          (fun d z => e.localFrame basis d z)
          (e.isLocalFrameOn_localFrame_baseSet I 1 basis) y)
        (frameComp0S (metricTensorField g) (fun d y => e.localFrame basis d y)) a x) ≤ B) :
    compL2 (iterCovCompU (I := I) (fun d y => e.localFrame basis d y)
      (fun y => christoffelSymbolInFrame (leviCivitaConnectionOfMetric G)
        (fun d z => e.localFrame basis d z)
        (e.isLocalFrameOn_localFrame_baseSet I 1 basis) y)
      (akCompField e g G basis) m x) ≤
    inverseContractionAffineRecurrenceConstant (C0 + 1) (3 / 2) (B + 1) m * (1 + B) := by
  let frame := fun d y => e.localFrame basis d y
  let hf := e.isLocalFrameOn_localFrame_baseSet I 1 basis
  let chr := fun y => christoffelSymbolInFrame (leviCivitaConnectionOfMetric G) frame hf y
  let gc := frameComp0S (metricTensorField g) frame
  let J := fun a y => compL2 (iterCovComp (I := I) frame chr gc a y)
  have heInv : ∀ᶠ y in 𝓝 x, compL2 (ginvCompField e g basis y) ≤ C0 + 1 := by
    have hc := continuousAt_ginv_compL2 e g basis hx
    exact (hc.eventually (gt_mem_nhds (lt_of_le_of_lt hInv (lt_add_one C0)))).mono
      (fun _ h => h.le)
  have heJet : ∀ a : Fin (m + 1), ∀ᶠ y in 𝓝 x, J (a.val + 1) y ≤ B + 1 := by
    intro a
    have ha : J (a.val + 1) x ≤ B := hJet (a.val + 1) (by omega) (by omega)
    have hc := continuousAt_metric_component_jet_norm e G g basis hx (a.val + 1)
    exact (hc.eventually (gt_mem_nhds (lt_of_le_of_lt ha (lt_add_one B)))).mono
      (fun _ h => h.le)
  have hN : {y | y ∈ e.baseSet ∧ compL2 (ginvCompField e g basis y) ≤ C0 + 1 ∧
      ∀ a : Fin (m + 1), J (a.val + 1) y ≤ B + 1} ∈ 𝓝 x := by
    filter_upwards [e.open_baseSet.mem_nhds hx, heInv, Filter.eventually_all.mpr heJet]
      with y hy hi hj
    exact ⟨hy, hi, hj⟩
  obtain ⟨V, hVN, hVopen, hxV⟩ := mem_nhds_iff.mp hN
  have hVbase : V ⊆ e.baseSet := fun _ hy => (hVN hy).1
  have hrec := iterated_covariant_tensor_bound_of_koszul_contraction hVopen frame chr
    (fun d => (frame_e_mdiffOn e basis d).mono hVbase)
    (fun d i k => (lcChrist_e_mdiffOn e G basis d i k).mono hVbase)
    (1 / 2) (1 / 2) (-(1 / 2))
    (Equiv.refl (Fin 3)) (Equiv.swap (0 : Fin 3) 1) ((finRotate 3).symm)
    (C0 + 1) (B + 1) m gc
    (fun k => (gCompField_mdiffOn e g basis k).mono hVbase)
    (ginvCompField e g basis) (akCompField e g G basis)
    (fun k => (akCompField_mdiffOn e g G basis k).mono hVbase)
    (fun y hy c d => ginv_hinv e g basis (hVbase hy) c d)
    (fun y hy => koszulComp_at frame hf e.open_baseSet g G (hVbase hy))
    (fun _ hy => (hVN hy).2.1)
    (fun y hy a ha ham => by
      have ha' := (hVN hy).2.2 ⟨a - 1, by omega⟩
      simpa only [show a - 1 + 1 = a by omega] using ha') x hxV
  norm_num at hrec
  have hc : 0 ≤ inverseContractionAffineRecurrenceConstant (C0 + 1) (3 / 2) (B + 1) m :=
    inverse_contraction_affine_recurrence_constant_nonneg _ _ _ _
  have htop := hJet (m + 1) (by omega) le_rfl
  change compL2 (iterCovCompU (I := I) frame chr (akCompField e g G basis) m x) ≤ _
  refine hrec.trans ?_
  exact mul_le_mul_of_nonneg_left (by linarith [htop]) hc

private theorem actual_tower_bound_at
    (G g : SmoothRiemannianMetric I M) (x : M) (m : ℕ)
    (ell B : ℝ) (hell : 0 < ell) (hB : 0 ≤ B)
    (hLower : ∀ v : TangentSpace I x, ell * G.inner x v v ≤ g.inner x v v)
    (hJet : ∀ a : ℕ, a ≤ m + 1 → metricDerivNorm a g G G x ≤ B) :
    Real.sqrt (normSq0S G x (3 + m)
      (iterCov G 3 (metricLoweredConnectionDifferenceField G g) m x)) ≤
    1 + Real.sqrt (Module.finrank ℝ E : ℝ) *
      inverseContractionAffineRecurrenceConstant
        (Real.sqrt (Module.finrank ℝ E : ℝ) / ell + 1) (3 / 2) (B + 1) m * (1 + B) := by
  classical
  obtain ⟨basis, hON⟩ := exists_trivONBasis G x
  let e := trivializationAt E (TangentSpace I : M → Type _) x
  let frame := fun d y => e.localFrame basis d y
  let hf := e.isLocalFrameOn_localFrame_baseSet I 1 basis
  let chr := fun y => christoffelSymbolInFrame (leviCivitaConnectionOfMetric G) frame hf y
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x
  have hinv : MetricInverseInBasis G x (hf.toBasisAt hx)
      (identityInvMetric (Idx := Fin (Module.finrank ℝ E))) := by
    apply metricInverseInBasis_identity_of_orthonormal
    intro i j
    simpa only [IsLocalFrameOn.toBasisAt_coe] using hON i j
  have hInv : compL2 (ginvCompField e g basis x) ≤
      Real.sqrt (Module.finrank ℝ E : ℝ) / ell := by
    have hi := ginv_compL2_le e g basis ell hell (fun v => by
      rw [gramE_dotVec]
      have h := hLower (∑ i, v i • e.localFrame basis i x)
      have hG : G.inner x (∑ i, v i • e.localFrame basis i x)
          (∑ i, v i • e.localFrame basis i x) = v ⬝ᵥ v := by
        rw [← gramE_dotVec, gramE_eq_one e G basis hON, Matrix.one_mulVec]
      rwa [hG] at h)
    simpa only [Fintype.card_fin] using hi
  have hcompJet : ∀ a, 1 ≤ a → a ≤ m + 1 →
      compL2 (iterCovComp (I := I) frame chr (frameComp0S (metricTensorField g) frame)
        a x) ≤ B := by
    intro a ha ham
    rw [compL2_tower_eq G (metricTensorField g) frame hf e.open_baseSet hx hinv a,
      ← metricCovDerivNorm_eq_iterCov g G a (hf.toBasisAt hx) hinv]
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
    have h := covNorm_le_add (r + 1) g G G x
    rw [covNorm_self_succ, zero_add] at h
    exact h.trans (hJet (r + 1) ham)
  have hA := component_tower_bound_at e G g basis hx m
    (Real.sqrt (Module.finrank ℝ E : ℝ) / ell) B hInv hcompJet
  have hGbase : compL2 (frameComp0S (metricTensorField G) frame x) ≤
      Real.sqrt (Module.finrank ℝ E : ℝ) := by
    have h := covNorm0_le G G x (C := 1) le_rfl (fun v => by simp)
    rw [one_mul] at h
    have h0 := compL2_tower_eq G (metricTensorField G) frame hf e.open_baseSet hx hinv 0
    have hn := metricCovDerivNorm_eq_iterCov G G 0 (hf.toBasisAt hx) hinv
    rw [← h0] at hn
    exact hn ▸ h
  have hL := lowered_tower_norm_le e G g basis hx hinv m
  have hR : 0 ≤ inverseContractionAffineRecurrenceConstant
      (Real.sqrt (Module.finrank ℝ E : ℝ) / ell + 1) (3 / 2) (B + 1) m :=
    inverse_contraction_affine_recurrence_constant_nonneg _ _ _ _
  have hprod := mul_le_mul hA hGbase (compL2_nonneg _)
    (mul_nonneg hR (by linarith : 0 ≤ 1 + B))
  exact (hL.trans hprod).trans (by nlinarith)

end DifferentialGeometry.Geometry.Connection

namespace DifferentialGeometry.Geometry.Connection

open TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem exists_connection_difference_derivative_bound_on_opens
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) E) (j : ℕ)
    (ell B : ℝ) (hell : 0 < ell) (hB : 0 ≤ B) :
    ∃ C > 0, ∀ (U : Opens E)
      (g : SmoothRiemannianMetric 𝓘(ℝ, E) U) (q : U),
      (∀ v : TangentSpace 𝓘(ℝ, E) q,
        ell * (G.restrictOpen U).inner q v v ≤ g.inner q v v) →
      (∀ a : ℕ, a ≤ j + 1 →
        metricDerivNorm a g (G.restrictOpen U) (G.restrictOpen U) q ≤ B) →
      Real.sqrt (normSq0S (G.restrictOpen U) q (3 + j)
        (iterCov (G.restrictOpen U) 3
          (metricLoweredConnectionDifferenceField (G.restrictOpen U) g) j q)) ≤ C := by
  let C := 1 + Real.sqrt (Module.finrank ℝ E : ℝ) *
    inverseContractionAffineRecurrenceConstant
      (Real.sqrt (Module.finrank ℝ E : ℝ) / ell + 1) (3 / 2) (B + 1) j * (1 + B)
  have hR := inverse_contraction_affine_recurrence_constant_nonneg
    (Real.sqrt (Module.finrank ℝ E : ℝ) / ell + 1) (3 / 2) (B + 1) j
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro U g q hLower hJet
  exact actual_tower_bound_at (G.restrictOpen U) g q j ell B hell hB hLower hJet

end DifferentialGeometry.Geometry.Connection
