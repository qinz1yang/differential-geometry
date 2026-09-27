import DifferentialGeometry.Geometry.Coordinates.Frame.Chart
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.TimeCoefficientContinuity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.Topology.Instances.Matrix

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold Filter Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology Bundle BigOperators Matrix

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]

section MatrixInverse

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem mvfderiv_eq_mfderiv_apply {f : M → ℝ} {x : M} {w : TangentSpace I x} :
    mvfderiv I f x w = (mfderiv I 𝓘(ℝ) f x) w := by
  rw [mvfderiv]
  rfl

private theorem mvfderiv_congr_of_eventuallyEq {f₁ f : M → ℝ} {x : M}
    (h : f₁ =ᶠ[𝓝 x] f) : mvfderiv I f₁ x = mvfderiv I f x := by
  have hx : f₁ x = f x := h.eq_of_nhds
  simp only [mvfderiv]
  rw [Filter.EventuallyEq.mfderiv_eq h, hx]

private theorem mvfzero_finset_prod {ι' : Type*} {s : Finset ι'} {g : ι' → M → ℝ} {x : M}
    {w : TangentSpace I x} (hg : ∀ i ∈ s, MDiffAt (g i) x)
    (h0 : ∀ i ∈ s, mvfderiv I (g i) x w = 0) :
    MDiffAt (fun p => ∏ i ∈ s, g i p) x ∧
      mvfderiv I (fun p => ∏ i ∈ s, g i p) x w = 0 := by
  classical
  induction s using Finset.induction with
  | empty =>
      constructor
      · simpa using mdifferentiableAt_const (I := I) (M := M) (I' := 𝓘(ℝ)) (M' := ℝ)
          (c := (1 : ℝ)) (x := x)
      · simp [mvfderiv_const]
  | insert a s ha ih =>
      have hga : MDiffAt (g a) x := hg a (Finset.mem_insert_self a s)
      have h0a : mvfderiv I (g a) x w = 0 := h0 a (Finset.mem_insert_self a s)
      have hgs : ∀ i ∈ s, MDiffAt (g i) x := fun i hi => hg i (Finset.mem_insert_of_mem hi)
      have h0s : ∀ i ∈ s, mvfderiv I (g i) x w = 0 := fun i hi => h0 i (Finset.mem_insert_of_mem hi)
      obtain ⟨hms, h0s'⟩ := ih hgs h0s
      have hfun : (fun p => ∏ i ∈ insert a s, g i p) = g a * fun p => ∏ i ∈ s, g i p := by
        funext p
        rw [Finset.prod_insert ha]
        rfl
      rw [hfun]
      refine ⟨hga.mul hms, ?_⟩
      rw [mvfderiv_mul hga hms]
      simp only [add_apply, smul_apply, smul_eq_mul, h0a, h0s', mul_zero, add_zero]

private theorem mvfzero_finset_sum {ι' : Type*} {s : Finset ι'} {g : ι' → M → ℝ} {x : M}
    {w : TangentSpace I x} (hg : ∀ i ∈ s, MDiffAt (g i) x)
    (h0 : ∀ i ∈ s, mvfderiv I (g i) x w = 0) :
    MDiffAt (fun p => ∑ i ∈ s, g i p) x ∧
      mvfderiv I (fun p => ∑ i ∈ s, g i p) x w = 0 := by
  classical
  induction s using Finset.induction with
  | empty =>
      constructor
      · simpa using mdifferentiableAt_const (I := I) (M := M) (I' := 𝓘(ℝ)) (M' := ℝ)
          (c := (0 : ℝ)) (x := x)
      · simp [mvfderiv_const]
  | insert a s ha ih =>
      have hga : MDiffAt (g a) x := hg a (Finset.mem_insert_self a s)
      have h0a : mvfderiv I (g a) x w = 0 := h0 a (Finset.mem_insert_self a s)
      have hgs : ∀ i ∈ s, MDiffAt (g i) x := fun i hi => hg i (Finset.mem_insert_of_mem hi)
      have h0s : ∀ i ∈ s, mvfderiv I (g i) x w = 0 := fun i hi => h0 i (Finset.mem_insert_of_mem hi)
      obtain ⟨hms, h0s'⟩ := ih hgs h0s
      have hfun : (fun p => ∑ i ∈ insert a s, g i p) = g a + fun p => ∑ i ∈ s, g i p := by
        funext p
        rw [Finset.sum_insert ha]
        rfl
      rw [hfun]
      refine ⟨hga.add hms, ?_⟩
      rw [mvfderiv_add hga hms]
      simp only [add_apply, h0a, h0s', add_zero]

private theorem mvfzero_const_mul (c : ℝ) {g : M → ℝ} {x : M} {w : TangentSpace I x}
    (hg : MDiffAt g x) (h0 : mvfderiv I g x w = 0) :
    MDiffAt (fun p => c * g p) x ∧ mvfderiv I (fun p => c * g p) x w = 0 := by
  have hc : MDiffAt (fun _ : M => c) x :=
    mdifferentiableAt_const (I := I) (M := M) (I' := 𝓘(ℝ)) (M' := ℝ) (c := c) (x := x)
  have hfun : (fun p => c * g p) = (fun _ : M => c) * g := rfl
  rw [hfun]
  refine ⟨hc.mul hg, ?_⟩
  rw [mvfderiv_mul hc hg]
  simp only [smul_apply, smul_eq_mul, mvfderiv_const, smul_zero, h0, mul_zero, add_zero]

private theorem mvfzero_det {G : M → Matrix ι ι ℝ} {x : M} {w : TangentSpace I x}
    (hG : ∀ i j, MDiffAt (fun p => G p i j) x)
    (h0 : ∀ i j, mvfderiv I (fun p => G p i j) x w = 0) :
    MDiffAt (fun p => (G p).det) x ∧ mvfderiv I (fun p => (G p).det) x w = 0 := by
  classical
  have hfun : (fun p => (G p).det) =
      fun p => ∑ σ : Equiv.Perm ι, (Equiv.Perm.sign σ : ℝ) * ∏ k, G p (σ k) k := by
    funext p
    rw [Matrix.det_apply]
    simp [Units.smul_def]
  rw [hfun]
  refine mvfzero_finset_sum (s := Finset.univ)
    (g := fun σ : Equiv.Perm ι => fun p => (Equiv.Perm.sign σ : ℝ) * ∏ k, G p (σ k) k) ?_ ?_
  · intro σ _
    obtain ⟨h1, h2⟩ := mvfzero_finset_prod (s := Finset.univ)
      (g := fun k => fun p => G p (σ k) k) (fun k _ => hG (σ k) k) (fun k _ => h0 (σ k) k)
    exact (mvfzero_const_mul _ h1 h2).1
  · intro σ _
    obtain ⟨h1, h2⟩ := mvfzero_finset_prod (s := Finset.univ)
      (g := fun k => fun p => G p (σ k) k) (fun k _ => hG (σ k) k) (fun k _ => h0 (σ k) k)
    exact (mvfzero_const_mul _ h1 h2).2

private theorem mvfzero_adjugate {G : M → Matrix ι ι ℝ} {x : M} {w : TangentSpace I x}
    (hG : ∀ i j, MDiffAt (fun p => G p i j) x)
    (h0 : ∀ i j, mvfderiv I (fun p => G p i j) x w = 0) (i j : ι) :
    MDiffAt (fun p => (G p).adjugate i j) x ∧
      mvfderiv I (fun p => (G p).adjugate i j) x w = 0 := by
  classical
  have hfun : (fun p => (G p).adjugate i j) =
      fun p => ((G p).updateRow j (Pi.single i 1)).det := by
    funext p
    rw [Matrix.adjugate_apply]
  rw [hfun]
  have hentry : ∀ a b : ι,
      (fun p => ((G p).updateRow j (Pi.single i 1)) a b) =
        ((if a = j then fun _ : M => (Pi.single i (1 : ℝ) : ι → ℝ) b
          else fun p => G p a b) : M → ℝ) := by
    intro a b
    by_cases haj : a = j
    · rw [if_pos haj, haj]
      funext p
      rw [Matrix.updateRow_self]
    · rw [if_neg haj]
      funext p
      rw [Matrix.updateRow_ne haj]
  refine mvfzero_det (G := fun p => (G p).updateRow j (Pi.single i 1)) ?_ ?_
  · intro a b
    rw [hentry a b]
    by_cases haj : a = j
    · rw [if_pos haj]
      exact mdifferentiableAt_const (I := I) (M := M) (I' := 𝓘(ℝ)) (M' := ℝ)
        (c := (Pi.single i (1 : ℝ) : ι → ℝ) b) (x := x)
    · rw [if_neg haj]
      exact hG a b
  · intro a b
    rw [hentry a b]
    by_cases haj : a = j
    · rw [if_pos haj]
      simp [mvfderiv_const]
    · rw [if_neg haj]
      exact h0 a b

theorem mvfderiv_matrix_inv_eq_zero_of_entry_mvfderiv_eq_zero {G : M → Matrix ι ι ℝ} {x : M}
    {w : TangentSpace I x}
    (hG : ∀ i j, MDiffAt (fun p => G p i j) x)
    (h0 : ∀ i j, mvfderiv I (fun p => G p i j) x w = 0)
    (hdet : (G x).det ≠ 0) (i j : ι) :
    mvfderiv I (fun p => (G p)⁻¹ i j) x w = 0 := by
  classical
  obtain ⟨hDdiff, hD0⟩ := mvfzero_det hG h0
  obtain ⟨hAddiff, hA0⟩ := mvfzero_adjugate hG h0 i j
  have hev : ∀ᶠ p in 𝓝 x, (G p).det ≠ 0 := hDdiff.continuousAt.eventually_ne hdet
  have hinvdiff : MDiffAt (fun p => ((G p).det)⁻¹) x := hDdiff.inv hdet
  have hinv0 : mvfderiv I (fun p => ((G p).det)⁻¹) x w = 0 := by
    have hmem : (fun p => ((G p).det)⁻¹) * (fun p => (G p).det)
        =ᶠ[𝓝 x] (fun _ : M => (1 : ℝ)) := by
      filter_upwards [hev] with p hp
      exact inv_mul_cancel₀ hp
    have h1 : mvfderiv I ((fun p => ((G p).det)⁻¹) * fun p => (G p).det) x w = 0 := by
      rw [mvfderiv_congr_of_eventuallyEq hmem]
      simp [mvfderiv_const]
    rw [mvfderiv_mul hinvdiff hDdiff] at h1
    simp only [add_apply, smul_apply, smul_eq_mul, hD0, mul_zero, zero_add] at h1
    exact (mul_eq_zero.mp h1).resolve_left hdet
  have hfun : (fun p => (G p)⁻¹ i j) =
      (fun p => ((G p).det)⁻¹) * (fun p => (G p).adjugate i j) := by
    funext p
    rw [Matrix.inv_def]
    simp [Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [hfun, mvfderiv_mul hinvdiff hAddiff]
  simp only [add_apply, smul_apply, smul_eq_mul, hinv0, hA0, mul_zero, add_zero]

end MatrixInverse

section FrameBasis

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M]

theorem exists_basis_apply_eq_of_frame (n : ℕ) (x : M)
    (v : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (V : Fin n → (y : M) → TangentSpace I y)
    (hVx : ∀ a, V a x = v a)
    (hVs : ∀ a, ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (fun y => (⟨y, V a y⟩ : TotalSpace E (TangentSpace I : M → Type _))) x) :
    ∃ basisOf : (p : M) → Module.Basis (Fin n) ℝ (TangentSpace I p),
      ∀ᶠ p in 𝓝 x, ∀ a, basisOf p a = V a p := by
  classical
  let e := trivializationAt E (TangentSpace I : M → Type _) x
  have hex : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hcoorde (a : Fin n) : ContMDiffAt I 𝓘(ℝ, E) 1
      (fun y => (e ⟨y, V a y⟩).2) x :=
    (e.contMDiffAt_section_iff (𝕜 := ℝ) (F := E) (E := TangentSpace I)
      (s := fun y => V a y) hex).mp (hVs a)
  let cle : E ≃L[ℝ] TangentSpace I x := e.continuousLinearEquivAt ℝ x hex
  let b : Module.Basis (Fin n) ℝ E := v.map cle.toLinearEquiv
  have hcard : n = Module.finrank ℝ E := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  let C : M → Matrix (Fin n) (Fin n) ℝ :=
    fun p => Matrix.of (fun a j => b.coord j ((e ⟨p, V a p⟩).2))
  have hCx : C x = 1 := by
    funext a j
    simp only [C, Matrix.of_apply, Matrix.one_apply]
    rw [hVx a]
    have hb : (e ⟨x, v a⟩).2 = b a := by
      rw [Trivialization.apply_eq_prod_continuousLinearEquivAt ℝ e x hex (v a)]
      rfl
    rw [hb, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  have hCcont : ContinuousAt C x := by
    apply continuousAt_pi.mpr
    intro a
    apply continuousAt_pi.mpr
    intro j
    have h1 : ContinuousAt (fun y => (e ⟨y, V a y⟩).2) x := (hcoorde a).continuousAt
    have h2 : Continuous (fun z : E => b.coord j z) := (b.coord j).continuous_of_finiteDimensional
    exact h2.continuousAt.comp h1
  have hdetx : (C x).det ≠ 0 := by
    rw [hCx, Matrix.det_one]
    exact one_ne_zero
  have hdetcont : ContinuousAt (fun p => (C p).det) x :=
    (Continuous.matrix_det continuous_id).continuousAt.comp hCcont
  have hev : ∀ᶠ p in 𝓝 x, (C p).det ≠ 0 := hdetcont.eventually_ne hdetx
  have hgood : ∀ᶠ p in 𝓝 x, (C p).det ≠ 0 ∧ p ∈ e.baseSet :=
    hev.and (e.open_baseSet.mem_nhds hex)
  have hindep : ∀ p, (C p).det ≠ 0 → p ∈ e.baseSet → LinearIndependent ℝ (fun a => V a p) := by
    intro p hdet hpb
    let w : Fin n → E := fun a => (e ⟨p, V a p⟩).2
    have hrow : LinearIndependent ℝ (C p).row :=
      Matrix.linearIndependent_row_iff.mpr (Matrix.nonsingular_iff_det_ne_zero.mpr hdet)
    have hrowE : LinearIndependent ℝ (fun a => b.equivFun (w a)) := by
      have heq : (fun a => b.equivFun (w a)) = (C p).row := by
        funext a j
        simp only [Matrix.row, C, Matrix.of_apply, Module.Basis.equivFun_apply,
          Module.Basis.coord_apply, w]
      rw [heq]
      exact hrow
    have hlinw : LinearIndependent ℝ w := by
      refine (Fintype.linearIndependent_iffₛ).mpr fun f g hfg i => ?_
      refine (Fintype.linearIndependent_iffₛ.mp hrowE) f g ?_ i
      funext j
      have h := congrArg (fun z : E => b.coord j z) hfg
      simpa only [map_sum, map_smul, Module.Basis.coord_apply, Module.Basis.equivFun_apply,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finsupp.coe_finsetSum,
        Finsupp.coe_smul] using h
    have hVw : ∀ a : Fin n, (e.continuousLinearEquivAt ℝ p hpb).symm (w a) = V a p := by
      intro a
      have hw : w a = e.continuousLinearEquivAt ℝ p hpb (V a p) := by
        simp only [w]
        rw [Trivialization.apply_eq_prod_continuousLinearEquivAt ℝ e p hpb (V a p)]
      rw [hw]
      exact (e.continuousLinearEquivAt ℝ p hpb).symm_apply_apply (V a p)
    have hlinV : LinearIndependent ℝ
        (fun a => (e.continuousLinearEquivAt ℝ p hpb).symm (w a)) :=
      hlinw.map' ((e.continuousLinearEquivAt ℝ p hpb).symm.toLinearMap)
        (LinearMap.ker_eq_bot.mpr (e.continuousLinearEquivAt ℝ p hpb).symm.injective)
    have hfin : (fun a => (e.continuousLinearEquivAt ℝ p hpb).symm (w a)) = fun a => V a p :=
      funext hVw
    rwa [hfin] at hlinV
  have hdef : ∀ p : M, Module.Basis (Fin n) ℝ (TangentSpace I p) := by
    intro p
    have hfd : FiniteDimensional ℝ (TangentSpace I p) :=
      inferInstanceAs (FiniteDimensional ℝ E)
    exact (Module.finBasis ℝ (TangentSpace I p)).reindex (finCongr hcard.symm)
  let hbasis : ∀ (p : M), (C p).det ≠ 0 → p ∈ e.baseSet →
      Module.Basis (Fin n) ℝ (TangentSpace I p) := fun p hdet hpb => by
    have hfd : FiniteDimensional ℝ (TangentSpace I p) :=
      inferInstanceAs (FiniteDimensional ℝ E)
    exact basisOfLinearIndependentOfCardEqFinrank' (fun a => V a p) (hindep p hdet hpb)
      (by rw [Fintype.card_fin]; exact hcard)
  refine ⟨fun p => if hp : (C p).det ≠ 0 ∧ p ∈ e.baseSet then hbasis p hp.1 hp.2
    else hdef p, ?_⟩
  filter_upwards [hgood] with p hp
  have hfd : FiniteDimensional ℝ (TangentSpace I p) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  rw [dif_pos hp]
  intro a
  exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' (fun a => V a p)
    (hindep p hp.1 hp.2) (by rw [Fintype.card_fin]; exact hcard)) a

end FrameBasis

section FrameInverseMetric

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] in
theorem mvfderiv_metricPairing_eq_zero_of_metricCompatible {n : ℕ} {x : M} {w : TangentSpace I x}
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {g : SmoothRiemannianMetric I M}
    (hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) cov g)
    (V : Fin n → (y : M) → TangentSpace I y)
    (hV : ∀ a, MDiffAt (fun y => (⟨y, V a y⟩ : TotalSpace E (TangentSpace I : M → Type _))) x)
    (hpar : ∀ a, cov (V a) x w = 0) (a b : Fin n) :
    mvfderiv I (fun p => g.inner p (V a p) (V b p)) x w = 0 := by
  let F : M → ℝ := fun p => g.inner p (V a p) (V b p)
  have h1 : (mfderiv I 𝓘(ℝ) F x) w = 0 := by
    have h := hmc (Y := V a) (Z := V b) (x := x) (hV a) (hV b) (Set.mem_univ x) w
    rw [hpar a, hpar b] at h
    have hz : (g.inner x) (0 : TangentSpace I x) (V b x) + (g.inner x) (V a x) 0 = 0 := by
      simp
    rw [hz] at h
    exact h
  have h2 : mvfderiv I F x w = 0 := by
    rw [mvfderiv_eq_mfderiv_apply]
    exact h1
  exact h2

theorem mvfderiv_basisInvMetric_eq_zero_of_parallel_frame {n : ℕ} {x : M} {w : TangentSpace I x}
    (g : SmoothRiemannianMetric I M)
    (V : Fin n → (y : M) → TangentSpace I y)
    (basisOf : (p : M) → Module.Basis (Fin n) ℝ (TangentSpace I p))
    (hbasis : ∀ᶠ p in 𝓝 x, ∀ a, basisOf p a = V a p)
    (hV : ∀ a b, MDiffAt (fun p => g.inner p (V a p) (V b p)) x)
    (h0 : ∀ a b, mvfderiv I (fun p => g.inner p (V a p) (V b p)) x w = 0)
    (i j : Fin n) :
    mvfderiv I (fun p => basisInvMetric (I := I) g p (basisOf p) i j) x w = 0 := by
  classical
  let Gram : M → Matrix (Fin n) (Fin n) ℝ :=
    fun p => Matrix.of (fun a b => g.inner p (V a p) (V b p))
  have hGram : ∀ a b, MDiffAt (fun p => Gram p a b) x := fun a b => hV a b
  have hGram0 : ∀ a b, mvfderiv I (fun p => Gram p a b) x w = 0 := fun a b => h0 a b
  have hbx : ∀ a, basisOf x a = V a x := hbasis.self_of_nhds
  have hprod : Matrix.of (basisInvMetric (I := I) g x (basisOf x)) * Gram x = 1 := by
    ext a b
    rw [Matrix.mul_apply, Matrix.one_apply]
    simpa only [Gram, Matrix.of_apply, hbx] using
      (basisInvMetric_isInverse (I := I) g x (basisOf x) a b).1
  have hdet : (Gram x).det ≠ 0 := Matrix.det_ne_zero_of_left_inverse hprod
  have hmain := mvfderiv_matrix_inv_eq_zero_of_entry_mvfderiv_eq_zero (I := I)
    (G := Gram) hGram hGram0 hdet i j
  have heq : (fun p => basisInvMetric (I := I) g p (basisOf p) i j)
      =ᶠ[𝓝 x] (fun p => (Gram p)⁻¹ i j) := by
    filter_upwards [hbasis] with p hp
    have hmat : Matrix.of (fun a b => g.inner p (basisOf p a) (basisOf p b)) = Gram p := by
      ext a b
      simp only [Gram, Matrix.of_apply]
      rw [hp a, hp b]
    rw [basisInvMetric_eq_matrix_inv (I := I) g (basisOf p), hmat]
  rw [mvfderiv_congr_of_eventuallyEq heq]
  exact hmain

theorem mvfderiv_basisInvMetric_eq_zero_of_metricCompatible_parallel_frame {n : ℕ} {x : M}
    {w : TangentSpace I x}
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {g : SmoothRiemannianMetric I M}
    (hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) cov g)
    (V : Fin n → (y : M) → TangentSpace I y)
    (basisOf : (p : M) → Module.Basis (Fin n) ℝ (TangentSpace I p))
    (hbasis : ∀ᶠ p in 𝓝 x, ∀ a, basisOf p a = V a p)
    (hV : ∀ a b, MDiffAt (fun p => g.inner p (V a p) (V b p)) x)
    (hVs : ∀ a, MDiffAt (fun y => (⟨y, V a y⟩ : TotalSpace E (TangentSpace I : M → Type _))) x)
    (hpar : ∀ a, cov (V a) x w = 0) (i j : Fin n) :
    mvfderiv I (fun p => basisInvMetric (I := I) g p (basisOf p) i j) x w = 0 :=
  mvfderiv_basisInvMetric_eq_zero_of_parallel_frame (I := I) g V basisOf hbasis hV
    (fun a b => mvfderiv_metricPairing_eq_zero_of_metricCompatible (I := I) hmc V hVs hpar a b)
    i j

end FrameInverseMetric

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
