import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Bounds.AllTimes

import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Algebra
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Solution.TimeRegularity
import DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Sections
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Ricci.Components
import DifferentialGeometry.Geometry.Metric.Convergence.Coordinates.GoodFrame
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Arity
import DifferentialGeometry.Geometry.Curvature.Bounds.RicciOperatorNorm
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.CovariantTwoTensor
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Scaling

/-!
# Background derivatives of an arbitrary covariant two-tensor

The Ricci tower of `RicciFlow/Compactness/Bounds/Ricci/Tower.lean` with the Ricci tensor replaced
by an arbitrary smooth covariant two-tensor `T`: intrinsic bounds on `∇_g^s T` (`s ≤ N`), uniform
equivalence of `g` with the background `gRef` and background bounds on `∇_{gRef}^r g` (`r < N`)
bound `∇_{gRef}^N T` affinely in `∇_{gRef}^N g`. The scaled form `velocity_tower_scaled` makes
the bound linear in the intrinsic bound, as needed for integrable metric velocities.
-/

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open scoped Manifold ContDiff Topology
open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates


variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [VectorBundle Real E (TangentSpace I : M → Type _)]
variable [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]

omit [I.Boundaryless] [IsManifold I 2 M] [T2Space M] [SigmaCompactSpace M]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
theorem velCompField_mdiffOn {Idx : Type*}
    (e₀ : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e₀]
    (T : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (basisE : Module.Basis Idx Real E) (k : Fin 2 → Idx) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y => frameComp0S (I := I) T (fun a y' => e₀.localFrame basisE a y') y k)
      e₀.baseSet := by
  intro y hy
  have hT : ContMDiffAt I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun x : M => Tensor0SSpace 2 I x) b (T b)) y :=
    T.contMDiff.contMDiffAt
  have hv : ∀ i : Fin 2,
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M => TotalSpace.mk' E (E := fun x : M => TangentSpace I x) b
          (e₀.localFrame basisE (k i) b)) y :=
    fun i => (frame_e_mdiffOn e₀ basisE (k i)).contMDiffAt (e₀.open_baseSet.mem_nhds hy)
  have h := TensorMultilinear.contMDiffAt_section_apply
    (T := fun b : M => T b) hT
    (v := fun (i : Fin 2) (b : M) => e₀.localFrame basisE (k i) b) hv
  exact h.contMDiffWithinAt

omit [Module.Finite ℝ E] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] [IsManifold I 2 M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
private theorem velNormSq0S_nonneg
    [Module.Finite ℝ E]
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (A : Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) :
    0 ≤ Tensor0SBundle.normSq0S (I := I) g x s A := by
  classical
  obtain ⟨basis, hON⟩ := Tensor0SBundle.exists_orthonormal_basis (I := I) g x
  have hinv : Tensor0SBundle.MetricInverseInBasis (I := I) g x basis
      (Tensor0SBundle.identityInvMetric
        (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    have h := Tensor0SBundle.metricInverseInBasis_of_orthonormal (I := I) g basis hON
    intro i j
    simpa [Tensor0SBundle.identityInvMetric, Tensor0SBundle.diagonalInvMetric] using h i j
  rw [Tensor0SBundle.normSq0S_identity_eq_sum_sq (I := I) g x s basis hinv A]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [Module.Finite ℝ E] [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    [IsManifold I 1 M] [I.Boundaryless] [IsManifold I 2 M]
    [SigmaCompactSpace M] in
private theorem velMcdNorm_eq_at
    [Module.Finite ℝ E]
    (h gRef : SmoothRiemannianMetric I M) (N : Nat) (x : M) :
    metricCovDerivNorm (I := I) N h gRef x =
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (2 + N)
        (iterCov (I := I) gRef 2
          (Tensor0SBundle.metricTensorField (I := I) h) N x)) := by
  classical
  obtain ⟨basis, hON⟩ := Tensor0SBundle.exists_orthonormal_basis (I := I) gRef x
  have hinv : Tensor0SBundle.MetricInverseInBasis (I := I) gRef x basis
      (Tensor0SBundle.identityInvMetric
        (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    have h' := Tensor0SBundle.metricInverseInBasis_of_orthonormal (I := I) gRef basis hON
    intro i j
    simpa [Tensor0SBundle.identityInvMetric, Tensor0SBundle.diagonalInvMetric] using h' i j
  exact metricCovDerivNorm_eq_iterCov (I := I) h gRef N basis hinv

private noncomputable def velKg (N : Nat) (Cg : Nat → Real) : Real :=
  ∑ j ∈ Finset.range N, 2 ^ (2 + j) * max (Cg j) 0

private noncomputable def velInvC (d : Nat) (Bmax : Real) : Real :=
  Real.sqrt d * (2 * Bmax)

private noncomputable def velShiC (N : Nat) (Bmax KShi : Real) : Real :=
  2 ^ (2 + N) * Bmax ^ (2 + N) * KShi

private noncomputable def velCL
    (d N : Nat) (Bmax : Real) (Cg : Nat → Real) (c : Nat) : Real :=
  inverseContractionAffineRecurrenceConstant (velInvC d Bmax) (3 / 2) (velKg N Cg) c

private noncomputable def velDBound
    (d N : Nat) (Bmax : Real) (Cg : Nat → Real) (c : Nat) : Real :=
  velCL d N Bmax Cg c * (1 + velKg N Cg)

private noncomputable def velCompC
    (d N : Nat) (Bmax : Real) (Cg : Nat → Real) (KShi : Real) : Real × Real :=
  aNConst 2 N (velDBound d N Bmax Cg)
    (velCL d N Bmax Cg (N - 1)) (velShiC N Bmax KShi)

private noncomputable def velFrameC (d : Nat) : Real :=
  (3 / 2) * ((d : Real) + 1)

structure VelTowerCoeffs where
  slope : Real
  offset : Real

noncomputable def velTowerCoeffs
    (d N : Nat) (Bmax : Real) (Cg : Nat → Real) (KShi : Real) :
    VelTowerCoeffs :=
  { slope := velFrameC d ^ (2 + N) *
      (velCompC d N Bmax Cg KShi).1 * 2 ^ (2 + N)
    offset := velFrameC d ^ (2 + N) *
      (velCompC d N Bmax Cg KShi).2 }

private theorem velKg_nonneg (N : Nat) (Cg : Nat → Real) :
    0 ≤ velKg N Cg := by
  exact Finset.sum_nonneg fun j _ => by positivity

private theorem velShiC_nonneg
    {N : Nat} {Bmax KShi : Real} (hBmax1 : 1 ≤ Bmax) (hKShi0 : 0 ≤ KShi) :
    0 ≤ velShiC N Bmax KShi := by
  unfold velShiC
  positivity

private theorem velCL_nonneg
    (d N : Nat) (Bmax : Real) (Cg : Nat → Real) (c : Nat) :
    0 ≤ velCL d N Bmax Cg c :=
  inverse_contraction_affine_recurrence_constant_nonneg _ _ _ _

private theorem velDBound_nonneg
    (d N : Nat) (Bmax : Real) (Cg : Nat → Real) (c : Nat) :
    0 ≤ velDBound d N Bmax Cg c := by
  exact mul_nonneg (velCL_nonneg d N Bmax Cg c)
    (by linarith [velKg_nonneg N Cg])

private theorem velCompC_fst_nonneg
    (d N : Nat) (Bmax : Real) (Cg : Nat → Real) (KShi : Real)
    (hBmax1 : 1 ≤ Bmax) (hKShi0 : 0 ≤ KShi) :
    0 ≤ (velCompC d N Bmax Cg KShi).1 :=
  aNConst_fst_nonneg (fun c => velDBound_nonneg d N Bmax Cg c)
    (velCL_nonneg d N Bmax Cg (N - 1))
    (velShiC_nonneg hBmax1 hKShi0)

private theorem velCompC_snd_nonneg
    (d N : Nat) (Bmax : Real) (Cg : Nat → Real) (KShi : Real)
    (hBmax1 : 1 ≤ Bmax) (hKShi0 : 0 ≤ KShi) :
    0 ≤ (velCompC d N Bmax Cg KShi).2 :=
  aNConst_snd_nonneg (fun c => velDBound_nonneg d N Bmax Cg c)
    (velCL_nonneg d N Bmax Cg (N - 1))
    (velShiC_nonneg hBmax1 hKShi0)

theorem velCoeffs_nonneg
    (d N : Nat) (Bmax : Real) (Cg : Nat → Real) (KShi : Real)
    (hBmax1 : 1 ≤ Bmax) (hKShi0 : 0 ≤ KShi) :
    0 ≤ (velTowerCoeffs d N Bmax Cg KShi).slope ∧
      0 ≤ (velTowerCoeffs d N Bmax Cg KShi).offset := by
  have hComp1 := velCompC_fst_nonneg d N Bmax Cg KShi hBmax1 hKShi0
  have hComp2 := velCompC_snd_nonneg d N Bmax Cg KShi hBmax1 hKShi0
  have hFrame : 0 ≤ velFrameC d := by
    unfold velFrameC
    positivity
  change
    0 ≤ velFrameC d ^ (2 + N) * (velCompC d N Bmax Cg KShi).1 * 2 ^ (2 + N) ∧
      0 ≤ velFrameC d ^ (2 + N) * (velCompC d N Bmax Cg KShi).2
  exact ⟨mul_nonneg (mul_nonneg (pow_nonneg hFrame _) hComp1) (by positivity),
    mul_nonneg (pow_nonneg hFrame _) hComp2⟩

omit [Module.Finite ℝ E] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem velPerDomain_bound
    [Module.Finite ℝ E]
    (gRef : SmoothRiemannianMetric I M)
    (e₀ : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e₀]
    (basisE : Module.Basis (Fin (Module.finrank Real E)) Real E)
    {w : Set M} (hwopen : IsOpen w) (hwsub : w ⊆ e₀.baseSet)
    (eps : Real) (heps0 : 0 ≤ eps)
    (hepsSm : (Fintype.card (Fin (Module.finrank Real E)) : Real) * eps ≤ 1 / 2)
    (hGnear : ∀ z ∈ w, ∀ i j : Fin (Module.finrank Real E),
      |gramE (I := I) e₀ gRef basisE z i j - (if i = j then 1 else 0)| ≤ eps)
    (hFwd : ∀ z, ∀ hz : z ∈ e₀.baseSet, z ∈ w →
      ∀ (s : ℕ) (A : Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) s z),
        (∑ I0 : Fin s → Fin (Module.finrank Real E),
          Tensor0SBundle.component0S (I := I)
            ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).toBasisAt hz) A I0 ^ 2) ≤
          2 ^ s * Tensor0SBundle.normSq0S (I := I) gRef z s A)
    (N : ℕ) (hN : 1 ≤ N)
    (Bmax : Real) (hBmax1 : 1 ≤ Bmax)
    (Cg : ℕ → Real)
    (KShi : Real) (hKShi0 : 0 ≤ KShi)
    (T : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2) :
      ∀ g : SmoothRiemannianMetric I M,
        (∀ z ∈ w, ∀ v : TangentSpace I z,
          Bmax⁻¹ * gRef.inner z v v ≤ g.inner z v v ∧
          Bmax⁻¹ * g.inner z v v ≤ gRef.inner z v v ∧
          gRef.inner z v v ≤ Bmax * g.inner z v v) →
        (∀ z ∈ w, ∀ j : ℕ, 1 ≤ j → j < N →
          metricCovDerivNorm (I := I) j g gRef z ≤ Cg j) →
        (∀ z ∈ w, ∀ s : ℕ, s ≤ N →
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g z (2 + s)
            (iterCov (I := I) g 2
              T s z)) ≤ KShi) →
        ∀ x ∈ w,
          compL2 (iterCovComp (I := I)
              (fun a y' => e₀.localFrame basisE a y')
              (fun y' => christoffelSymbolInFrame
                (leviCivitaConnectionOfMetric (I := I) gRef)
                (fun a y'' => e₀.localFrame basisE a y'')
                ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).mono hwsub) y')
              (frameComp0S (I := I)
                T
                (fun a y' => e₀.localFrame basisE a y')) N x) ≤
            (velCompC (Module.finrank Real E) N Bmax Cg KShi).1 *
              compL2 (iterCovComp (I := I)
              (fun a y' => e₀.localFrame basisE a y')
              (fun y' => christoffelSymbolInFrame
                (leviCivitaConnectionOfMetric (I := I) gRef)
                (fun a y'' => e₀.localFrame basisE a y'')
                ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).mono hwsub) y')
              (frameComp0S (I := I) (metricTensorField (I := I) g)
                (fun a y' => e₀.localFrame basisE a y')) N x) +
              (velCompC (Module.finrank Real E) N Bmax Cg KShi).2 := by
  classical
  have hBmax0 : (0 : Real) < Bmax := lt_of_lt_of_le one_pos hBmax1
  have hKg0 : 0 ≤ velKg N Cg := velKg_nonneg N Cg
  have hKShiC0 : 0 ≤ velShiC N Bmax KShi :=
    velShiC_nonneg hBmax1 hKShi0
  have hCLb := fun c : ℕ => connection_difference_component_bound_in_frame (I := I) hwopen gRef
    (fun a y' => e₀.localFrame basisE a y')
    ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).mono hwsub)
    (fun d => (frame_e_mdiffOn e₀ basisE d).mono hwsub)
    (fun d i j => ((lcChrist_e_mdiffOn e₀ gRef basisE d i j).mono hwsub).congr
      (fun z hz => chrInFrame_mono (I := I) (leviCivitaConnectionOfMetric (I := I) gRef)
        (fun a y' => e₀.localFrame basisE a y')
        (e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE) hwsub hz d i j))
    (velInvC (Module.finrank Real E) Bmax) (velKg N Cg) c
  have hCL0 := fun c : ℕ =>
    velCL_nonneg (Module.finrank Real E) N Bmax Cg c
  have haN := aN_component_bound (r₀ := 2) (rg := 2) (I := I) hwopen
    (fun a y' => e₀.localFrame basisE a y')
    (fun y' => christoffelSymbolInFrame
      (leviCivitaConnectionOfMetric (I := I) gRef)
      (fun a y'' => e₀.localFrame basisE a y'')
      ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).mono hwsub) y')
    (fun d => (frame_e_mdiffOn e₀ basisE d).mono hwsub)
    (fun d i j => ((lcChrist_e_mdiffOn e₀ gRef basisE d i j).mono hwsub).congr
      (fun z hz => chrInFrame_mono (I := I) (leviCivitaConnectionOfMetric (I := I) gRef)
        (fun a y' => e₀.localFrame basisE a y')
        (e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE) hwsub hz d i j))
    N hN (velDBound (Module.finrank Real E) N Bmax Cg)
    (fun c => velDBound_nonneg (Module.finrank Real E) N Bmax Cg c)
    (velCL (Module.finrank Real E) N Bmax Cg (N - 1))
    (velShiC N Bmax KShi) hKShiC0
  intro g hequivW hmcd hShiPt x hx
  have hchrGw : ∀ d i j : Fin (Module.finrank Real E), ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y => christoffelSymbolInFrame
        (leviCivitaConnectionOfMetric (I := I) g)
        (fun a y'' => e₀.localFrame basisE a y'')
        ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).mono hwsub) y d i j) w :=
    fun d i j => ((lcChrist_e_mdiffOn e₀ g basisE d i j).mono hwsub).congr
      (fun z hz => chrInFrame_mono (I := I) (leviCivitaConnectionOfMetric (I := I) g)
        (fun a y' => e₀.localFrame basisE a y')
        (e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE) hwsub hz d i j)
  have hgsmW := fun k => (gCompField_mdiffOn e₀ g basisE k).mono hwsub
  have hRicSmW := fun k => (velCompField_mdiffOn e₀ T basisE k).mono hwsub
  have hGinvW : ∀ z ∈ w, compL2 (ginvCompField (I := I) e₀ g basisE z) ≤
      velInvC (Module.finrank Real E) Bmax := by
    intro z hz
    simpa only [velInvC, Fintype.card_fin] using
      movingGinv_le (I := I) e₀ g gRef basisE Bmax hBmax0
        (fun v => (hequivW z hz v).1) eps heps0 hepsSm (fun i j => hGnear z hz i j)
  have hinvW : ∀ z ∈ w, ∀ c e : Fin (Module.finrank Real E),
      (∑ l, frameComp0S (I := I) (metricTensorField (I := I) g)
          (fun a y' => e₀.localFrame basisE a y') z
          (Fin.snoc (fun _ : Fin 1 => l) c) *
        ginvCompField (I := I) e₀ g basisE z (Fin.snoc (fun _ : Fin 1 => e) l)) =
      if c = e then 1 else 0 :=
    fun z hz c e => ginv_hinv (I := I) e₀ g basisE (hwsub hz) c e
  have hgB : ∀ z ∈ w, ∀ j : ℕ, 1 ≤ j → j ≤ N - 1 →
      compL2 (iterCovComp (I := I)
        (fun a y' => e₀.localFrame basisE a y')
        (fun y' => christoffelSymbolInFrame
          (leviCivitaConnectionOfMetric (I := I) gRef)
          (fun a y'' => e₀.localFrame basisE a y'')
          ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).mono hwsub) y')
        (frameComp0S (I := I) (metricTensorField (I := I) g)
          (fun a y' => e₀.localFrame basisE a y')) j z) ≤ velKg N Cg := by
    intro z hz j h1 hjN
    have htow := compL2_tower_le (I := I) gRef gRef
      (Tensor0SBundle.metricTensorField (I := I) g)
      (fun a y' => e₀.localFrame basisE a y')
      ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).mono hwsub) hwopen hz
      (fun s A => hFwd z (hwsub hz) hz s A) j
    have hmc := velMcdNorm_eq_at (I := I) g gRef j z
    have hcg := hmcd z hz j h1 (by omega)
    have hKgterm : (2 : Real) ^ (2 + j) * max (Cg j) 0 ≤ velKg N Cg := by
      rw [velKg]
      exact Finset.single_le_sum
        (f := fun j' => (2 : Real) ^ (2 + j') * max (Cg j') 0)
        (fun j' _ => by positivity) (Finset.mem_range.mpr (by omega))
    have h2p : (0 : Real) ≤ 2 ^ (2 + j) := by positivity
    calc compL2 (iterCovComp (I := I)
          (fun a y' => e₀.localFrame basisE a y')
          (fun y' => christoffelSymbolInFrame
            (leviCivitaConnectionOfMetric (I := I) gRef)
            (fun a y'' => e₀.localFrame basisE a y'')
            ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).mono hwsub) y')
          (frameComp0S (I := I) (metricTensorField (I := I) g)
            (fun a y' => e₀.localFrame basisE a y')) j z)
        ≤ 2 ^ (2 + j) * Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef z (2 + j)
            (iterCov (I := I) gRef 2
              (Tensor0SBundle.metricTensorField (I := I) g) j z)) := htow
      _ = 2 ^ (2 + j) * metricCovDerivNorm (I := I) j g gRef z := by rw [hmc]
      _ ≤ 2 ^ (2 + j) * max (Cg j) 0 :=
          mul_le_mul_of_nonneg_left (le_trans hcg (le_max_left _ _)) h2p
      _ ≤ velKg N Cg := hKgterm
  have hDlow : ∀ c : ℕ, c < N - 1 → ∀ z ∈ w,
      compL2 (iterCovCompU (I := I)
        (fun a y' => e₀.localFrame basisE a y')
        (fun y' => christoffelSymbolInFrame
          (leviCivitaConnectionOfMetric (I := I) gRef)
          (fun a y'' => e₀.localFrame basisE a y'')
          ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).mono hwsub) y')
        (christoffelDifferenceField
          (fun y' => christoffelSymbolInFrame
            (leviCivitaConnectionOfMetric (I := I) g)
            (fun a y'' => e₀.localFrame basisE a y'')
            ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).mono hwsub) y')
          (fun y' => christoffelSymbolInFrame
            (leviCivitaConnectionOfMetric (I := I) gRef)
            (fun a y'' => e₀.localFrame basisE a y'')
            ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).mono hwsub) y')) c z) ≤
      velDBound (Module.finrank Real E) N Bmax Cg c := by
    intro c hc z hz
    have h := hCLb c g hchrGw hgsmW (ginvCompField (I := I) e₀ g basisE)
      hinvW hGinvW (fun z' hz' j h1 h2 => hgB z' hz' j h1 (by omega)) z hz
    have hg := hgB z hz (c + 1) (by omega) (by omega)
    have hnn : (0 : Real) ≤ compL2 (iterCovComp (I := I)
        (fun a y' => e₀.localFrame basisE a y')
        (fun y' => christoffelSymbolInFrame
          (leviCivitaConnectionOfMetric (I := I) gRef)
          (fun a y'' => e₀.localFrame basisE a y'')
          ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).mono hwsub) y')
        (frameComp0S (I := I) (metricTensorField (I := I) g)
          (fun a y' => e₀.localFrame basisE a y')) (c + 1) z) := compL2_nonneg _
    rw [velDBound, velCL]
    exact h.trans
      (mul_le_mul_of_nonneg_left (by nlinarith [hg]) (hCL0 c))
  have hDtop : ∀ z ∈ w,
      compL2 (iterCovCompU (I := I)
        (fun a y' => e₀.localFrame basisE a y')
        (fun y' => christoffelSymbolInFrame
          (leviCivitaConnectionOfMetric (I := I) gRef)
          (fun a y'' => e₀.localFrame basisE a y'')
          ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).mono hwsub) y')
        (christoffelDifferenceField
          (fun y' => christoffelSymbolInFrame
            (leviCivitaConnectionOfMetric (I := I) g)
            (fun a y'' => e₀.localFrame basisE a y'')
            ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).mono hwsub) y')
          (fun y' => christoffelSymbolInFrame
            (leviCivitaConnectionOfMetric (I := I) gRef)
            (fun a y'' => e₀.localFrame basisE a y'')
            ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).mono hwsub) y')) (N - 1) z) ≤
      velCL (Module.finrank Real E) N Bmax Cg (N - 1) *
        (1 + compL2 (iterCovComp (I := I)
        (fun a y' => e₀.localFrame basisE a y')
        (fun y' => christoffelSymbolInFrame
          (leviCivitaConnectionOfMetric (I := I) gRef)
          (fun a y'' => e₀.localFrame basisE a y'')
          ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).mono hwsub) y')
        (frameComp0S (I := I) (metricTensorField (I := I) g)
          (fun a y' => e₀.localFrame basisE a y')) N z)) := by
    intro z hz
    have h := hCLb (N - 1) g hchrGw hgsmW (ginvCompField (I := I) e₀ g basisE)
      hinvW hGinvW (fun z' hz' j h1 h2 => hgB z' hz' j h1 h2) z hz
    rw [show N - 1 + 1 = N from by omega] at h
    simpa only [velCL] using h
  have hShiComp : ∀ z ∈ w, ∀ s : ℕ, s ≤ N →
      compL2 (iterCovComp (I := I)
        (fun a y' => e₀.localFrame basisE a y')
        (fun y' => christoffelSymbolInFrame
          (leviCivitaConnectionOfMetric (I := I) g)
          (fun a y'' => e₀.localFrame basisE a y'')
          ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).mono hwsub) y')
        (frameComp0S (I := I)
          T
          (fun a y' => e₀.localFrame basisE a y')) s z) ≤ velShiC N Bmax KShi := by
    intro z hz s hsN
    have htow := compL2_tower_le (I := I) g gRef
      T
      (fun a y' => e₀.localFrame basisE a y')
      ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).mono hwsub) hwopen hz
      (fun s' A => hFwd z (hwsub hz) hz s' A) s
    have hswap := (Tensor0SBundle.normSq0S_le_of_metric_equiv (I := I) g gRef z (2 + s)
      hBmax1 (fun v => ⟨(hequivW z hz v).2.1, (hequivW z hz v).2.2⟩)
      (iterCov (I := I) g 2
        T s z)).2
    rw [zpow_natCast] at hswap
    have hnn := velNormSq0S_nonneg (I := I) g z (2 + s)
      (iterCov (I := I) g 2
        T s z)
    have hsqv := hShiPt z hz s hsN
    have hval : Tensor0SBundle.normSq0S (I := I) g z (2 + s)
        (iterCov (I := I) g 2
          T s z) ≤ KShi ^ 2 := by
      calc Tensor0SBundle.normSq0S (I := I) g z (2 + s)
            (iterCov (I := I) g 2
              T s z)
          = Real.sqrt (Tensor0SBundle.normSq0S (I := I) g z (2 + s)
              (iterCov (I := I) g 2
                T s z)) ^ 2 := (Real.sq_sqrt hnn).symm
        _ ≤ KShi ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqv 2
    have hBp : (0 : Real) ≤ Bmax ^ (2 + s) := by positivity
    have hgRefBound : Tensor0SBundle.normSq0S (I := I) gRef z (2 + s)
        (iterCov (I := I) g 2
          T s z) ≤ Bmax ^ (2 + s) * KShi ^ 2 :=
      le_trans hswap (mul_le_mul_of_nonneg_left hval hBp)
    have hsqrtBound : Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef z (2 + s)
        (iterCov (I := I) g 2
          T s z)) ≤ Bmax ^ (2 + s) * KShi := by
      calc Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef z (2 + s)
            (iterCov (I := I) g 2
              T s z))
          ≤ Real.sqrt (Bmax ^ (2 + s) * KShi ^ 2) := Real.sqrt_le_sqrt hgRefBound
        _ = Real.sqrt (Bmax ^ (2 + s)) * Real.sqrt (KShi ^ 2) :=
            Real.sqrt_mul (by positivity) _
        _ = Real.sqrt (Bmax ^ (2 + s)) * KShi := by
            rw [Real.sqrt_sq hKShi0]
        _ ≤ Bmax ^ (2 + s) * KShi := by
            refine mul_le_mul_of_nonneg_right ?_ hKShi0
            have h2 : (Bmax ^ (2 + s)) ≤ (Bmax ^ (2 + s)) ^ 2 := by
              have h1 : (1 : Real) ≤ Bmax ^ (2 + s) := one_le_pow₀ hBmax1
              nlinarith
            calc Real.sqrt (Bmax ^ (2 + s))
                ≤ Real.sqrt ((Bmax ^ (2 + s)) ^ 2) := Real.sqrt_le_sqrt h2
              _ = Bmax ^ (2 + s) := Real.sqrt_sq (by positivity)
    have h2mono : (2 : Real) ^ (2 + s) ≤ 2 ^ (2 + N) :=
      pow_le_pow_right₀ one_le_two (by omega)
    have hBmono : Bmax ^ (2 + s) ≤ Bmax ^ (2 + N) :=
      pow_le_pow_right₀ hBmax1 (by omega)
    calc compL2 (iterCovComp (I := I)
          (fun a y' => e₀.localFrame basisE a y')
          (fun y' => christoffelSymbolInFrame
            (leviCivitaConnectionOfMetric (I := I) g)
            (fun a y'' => e₀.localFrame basisE a y'')
            ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).mono hwsub) y')
          (frameComp0S (I := I)
            T
            (fun a y' => e₀.localFrame basisE a y')) s z)
        ≤ 2 ^ (2 + s) * Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef z (2 + s)
            (iterCov (I := I) g 2
              T s z)) := htow
      _ ≤ 2 ^ (2 + s) * (Bmax ^ (2 + s) * KShi) :=
          mul_le_mul_of_nonneg_left hsqrtBound (by positivity)
      _ ≤ 2 ^ (2 + N) * (Bmax ^ (2 + N) * KShi) := by
          have hb : Bmax ^ (2 + s) * KShi ≤ Bmax ^ (2 + N) * KShi :=
            mul_le_mul_of_nonneg_right hBmono hKShi0
          have hnn2 : (0 : Real) ≤ Bmax ^ (2 + s) * KShi := by positivity
          calc (2 : Real) ^ (2 + s) * (Bmax ^ (2 + s) * KShi)
              ≤ 2 ^ (2 + N) * (Bmax ^ (2 + s) * KShi) :=
                mul_le_mul_of_nonneg_right h2mono hnn2
            _ ≤ 2 ^ (2 + N) * (Bmax ^ (2 + N) * KShi) :=
                mul_le_mul_of_nonneg_left hb (by positivity)
      _ = velShiC N Bmax KShi := by rw [velShiC]; ring
  exact haN
    (fun y' => christoffelSymbolInFrame
      (leviCivitaConnectionOfMetric (I := I) g)
      (fun a y'' => e₀.localFrame basisE a y'')
      ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).mono hwsub) y')
    hchrGw
    (frameComp0S (I := I)
      T
      (fun a y' => e₀.localFrame basisE a y'))
    hRicSmW hDlow
    (frameComp0S (I := I) (metricTensorField (I := I) g)
      (fun a y' => e₀.localFrame basisE a y'))
    hDtop hShiComp x hx

omit [Module.Finite ℝ E] [I.Boundaryless] [SigmaCompactSpace M] in
theorem velocity_tower_on
    [Module.Finite ℝ E]
    {U : Set M} (hU : IsOpen U)
    (gRef g : SmoothRiemannianMetric I M)
    (T : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (N : Nat) (hN : 1 ≤ N)
    (Bmax : Real) (hBmax1 : 1 ≤ Bmax)
    (Cg : Nat → Real)
    (KShi : Real) (hKShi0 : 0 ≤ KShi)
    (hequiv : MetricUniformEquivalentOn (I := I) U gRef g Bmax)
    (hBprev : ∀ r : Nat, 1 ≤ r → r < N → ∀ x ∈ U,
      metricCovDerivNorm (I := I) r g gRef x ≤ Cg r)
    (hShi : ∀ s : Nat, s ≤ N → ∀ x ∈ U,
      Real.sqrt
        (Tensor0SBundle.normSq0S (I := I) g x (2 + s)
          (iterCov (I := I) g 2 T s x)) ≤ KShi) :
    ∀ x ∈ U,
      Real.sqrt
        (Tensor0SBundle.normSq0S (I := I) gRef x (2 + N)
          (iterCov (I := I) gRef 2 T N x)) ≤
        (velTowerCoeffs (Module.finrank Real E) N Bmax Cg KShi).slope *
            metricCovDerivNorm (I := I) N g gRef x +
          (velTowerCoeffs (Module.finrank Real E) N Bmax Cg KShi).offset := by
  classical
  intro x hxU
  obtain ⟨basisE, u', eps, hopen, hxu, hsubB, heps0, hepsSm, hGnear,
      _hON, hFwd, hRev⟩ := exists_goodFrame_compBound (I := I) gRef x
  have hwopen : IsOpen (u' ∩ U) := hopen.inter hU
  have hxw : x ∈ u' ∩ U := ⟨hxu, hxU⟩
  have hwsub : u' ∩ U ⊆
      (trivializationAt E (TangentSpace I : M → Type _) x).baseSet :=
    Set.inter_subset_left.trans hsubB
  have hequivSymm := metricUniformEquivalentOn_symm (I := I) hequiv
  have hpack : ∀ z ∈ u' ∩ U, ∀ v : TangentSpace I z,
      Bmax⁻¹ * gRef.inner z v v ≤ g.inner z v v ∧
      Bmax⁻¹ * g.inner z v v ≤ gRef.inner z v v ∧
      gRef.inner z v v ≤ Bmax * g.inner z v v := by
    intro z hz v
    exact ⟨(hequiv.2 z hz.2 v).1, (hequivSymm.2 z hz.2 v).1,
      (hequivSymm.2 z hz.2 v).2⟩
  have hmcdW : ∀ z ∈ u' ∩ U, ∀ j : Nat, 1 ≤ j → j < N →
      metricCovDerivNorm (I := I) j g gRef z ≤ Cg j :=
    fun z hz j h1 hj => hBprev j h1 hj z hz.2
  have hShiW : ∀ z ∈ u' ∩ U, ∀ s : Nat, s ≤ N →
      Real.sqrt
        (Tensor0SBundle.normSq0S (I := I) g z (2 + s)
          (iterCov (I := I) g 2 T s z)) ≤ KShi :=
    fun z hz s hs => hShi s hs z hz.2
  have hAN := velPerDomain_bound (I := I) gRef
    (trivializationAt E (TangentSpace I : M → Type _) x) basisE
    hwopen hwsub eps heps0 hepsSm
    (fun z hz i j => hGnear z hz.1 i j)
    (fun z hz hzw s A => hFwd z hz hzw.1 s A)
    N hN Bmax hBmax1 Cg KShi hKShi0 T g hpack hmcdW hShiW x hxw
  have hxbase : x ∈
      (trivializationAt E (TangentSpace I : M → Type _) x).baseSet :=
    hsubB hxu
  have hCu1 : (1 : Real) ≤ velFrameC (Module.finrank Real E) := by
    unfold velFrameC
    have hd0 : (0 : Real) ≤ Module.finrank Real E := Nat.cast_nonneg _
    nlinarith
  have hCuP0 : (0 : Real) ≤ velFrameC (Module.finrank Real E) ^ (2 + N) := by
    positivity
  have hframeBase :=
    (trivializationAt E (TangentSpace I : M → Type _) x)
      |>.isLocalFrameOn_localFrame_baseSet I 1 basisE
  have hframeW := hframeBase.mono hwsub
  have hLHS := sqrt_tower_le_compL2 (I := I) gRef
    T
    (fun a y' => (trivializationAt E (TangentSpace I : M → Type _) x).localFrame
      basisE a y')
    hframeW
    hwopen hxw (velFrameC (Module.finrank Real E)) hCu1
    (fun s A => by
      have hsum :
          (∑ I0, Tensor0SBundle.component0S (I := I)
            (hframeW.toBasisAt hxw) A I0 ^ 2) =
            ∑ I0, Tensor0SBundle.component0S (I := I)
              (hframeBase.toBasisAt hxbase) A I0 ^ 2 := by
        apply Finset.sum_congr rfl
        intro I0 _
        congr 1
      rw [velFrameC, hsum]
      simpa only [Fintype.card_fin] using hRev x hxbase hxu s A) N
  have hRHS := compL2_tower_le (I := I) gRef gRef
    (Tensor0SBundle.metricTensorField (I := I) g)
    (fun a y' => (trivializationAt E (TangentSpace I : M → Type _) x).localFrame
      basisE a y')
    (((trivializationAt E (TangentSpace I : M → Type _) x).isLocalFrameOn_localFrame_baseSet
      I 1 basisE).mono hwsub)
    hwopen hxw (fun s A => hFwd x hxbase hxu s A) N
  have hmc := velMcdNorm_eq_at (I := I) g gRef N x
  have hComp0 :
      0 ≤ (velCompC (Module.finrank Real E) N Bmax Cg KShi).1 :=
    velCompC_fst_nonneg (Module.finrank Real E) N Bmax Cg KShi hBmax1 hKShi0
  calc
    Real.sqrt
        (Tensor0SBundle.normSq0S (I := I) gRef x (2 + N)
          (iterCov (I := I) gRef 2 T N x))
        ≤ velFrameC (Module.finrank Real E) ^ (2 + N) *
            compL2 (iterCovComp (I := I)
              (fun a y' => (trivializationAt E
                (TangentSpace I : M → Type _) x).localFrame basisE a y')
              (fun y' => christoffelSymbolInFrame
                (leviCivitaConnectionOfMetric (I := I) gRef)
                (fun a y'' => (trivializationAt E
                  (TangentSpace I : M → Type _) x).localFrame basisE a y'')
                (((trivializationAt E
                  (TangentSpace I : M → Type _) x).isLocalFrameOn_localFrame_baseSet
                    I 1 basisE).mono hwsub) y')
              (frameComp0S (I := I)
                T
                (fun a y' => (trivializationAt E
                  (TangentSpace I : M → Type _) x).localFrame basisE a y')) N x) := hLHS
    _ ≤ velFrameC (Module.finrank Real E) ^ (2 + N) *
          ((velCompC (Module.finrank Real E) N Bmax Cg KShi).1 *
              compL2 (iterCovComp (I := I)
                (fun a y' => (trivializationAt E
                  (TangentSpace I : M → Type _) x).localFrame basisE a y')
                (fun y' => christoffelSymbolInFrame
                  (leviCivitaConnectionOfMetric (I := I) gRef)
                  (fun a y'' => (trivializationAt E
                    (TangentSpace I : M → Type _) x).localFrame basisE a y'')
                  (((trivializationAt E
                    (TangentSpace I : M → Type _) x).isLocalFrameOn_localFrame_baseSet
                      I 1 basisE).mono hwsub) y')
                (frameComp0S (I := I) (metricTensorField (I := I) g)
                  (fun a y' => (trivializationAt E
                    (TangentSpace I : M → Type _) x).localFrame basisE a y')) N x) +
            (velCompC (Module.finrank Real E) N Bmax Cg KShi).2) :=
      mul_le_mul_of_nonneg_left hAN hCuP0
    _ ≤ velFrameC (Module.finrank Real E) ^ (2 + N) *
          ((velCompC (Module.finrank Real E) N Bmax Cg KShi).1 *
              (2 ^ (2 + N) * metricCovDerivNorm (I := I) N g gRef x) +
            (velCompC (Module.finrank Real E) N Bmax Cg KShi).2) := by
      refine mul_le_mul_of_nonneg_left ?_ hCuP0
      refine add_le_add ?_ le_rfl
      refine mul_le_mul_of_nonneg_left ?_ hComp0
      calc
        compL2 (iterCovComp (I := I)
            (fun a y' => (trivializationAt E
              (TangentSpace I : M → Type _) x).localFrame basisE a y')
            (fun y' => christoffelSymbolInFrame
              (leviCivitaConnectionOfMetric (I := I) gRef)
              (fun a y'' => (trivializationAt E
                (TangentSpace I : M → Type _) x).localFrame basisE a y'')
              (((trivializationAt E
                (TangentSpace I : M → Type _) x).isLocalFrameOn_localFrame_baseSet
                  I 1 basisE).mono hwsub) y')
            (frameComp0S (I := I) (metricTensorField (I := I) g)
              (fun a y' => (trivializationAt E
                (TangentSpace I : M → Type _) x).localFrame basisE a y')) N x)
            ≤ 2 ^ (2 + N) *
                Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (2 + N)
                  (iterCov (I := I) gRef 2
                    (Tensor0SBundle.metricTensorField (I := I) g) N x)) := hRHS
        _ = 2 ^ (2 + N) * metricCovDerivNorm (I := I) N g gRef x := by
          rw [hmc]
    _ = (velTowerCoeffs (Module.finrank Real E) N Bmax Cg KShi).slope *
          metricCovDerivNorm (I := I) N g gRef x +
        (velTowerCoeffs (Module.finrank Real E) N Bmax Cg KShi).offset := by
      change
        velFrameC (Module.finrank Real E) ^ (2 + N) *
            ((velCompC (Module.finrank Real E) N Bmax Cg KShi).1 *
                (2 ^ (2 + N) * metricCovDerivNorm (I := I) N g gRef x) +
              (velCompC (Module.finrank Real E) N Bmax Cg KShi).2) =
          (velFrameC (Module.finrank Real E) ^ (2 + N) *
              (velCompC (Module.finrank Real E) N Bmax Cg KShi).1 * 2 ^ (2 + N)) *
              metricCovDerivNorm (I := I) N g gRef x +
            velFrameC (Module.finrank Real E) ^ (2 + N) *
              (velCompC (Module.finrank Real E) N Bmax Cg KShi).2
      ring

omit [I.Boundaryless] [SigmaCompactSpace M] [IsManifold I 2 M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
private theorem velNorm_eq_sqrt_iterCov [CompleteSpace E]
    (T : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) :
    tensor02CovDerivNormWith (I := I) s T g g x =
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x (2 + s) (iterCov (I := I) g 2 T s x)) := by
  classical
  obtain ⟨basis, hON⟩ := Tensor0SBundle.exists_orthonormal_basis (I := I) g x
  exact tensor02CovDerivNormWith_eq_iterCov (I := I) T g s basis
    (Tensor0SBundle.metricInverseInBasis_of_orthonormal (I := I) g basis hON)

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem velocity_tower_scaled [CompleteSpace E]
    (gRef g : SmoothRiemannianMetric I M)
    (T : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (N : ℕ) (hN : 1 ≤ N) (Bmax : ℝ) (hBmax1 : 1 ≤ Bmax) (Cg : ℕ → ℝ)
    (hequiv : MetricUniformEquivalentOn (I := I) Set.univ gRef g Bmax)
    (hBprev : ∀ r : ℕ, 1 ≤ r → r < N → ∀ x : M,
      metricCovDerivNorm (I := I) r g gRef x ≤ Cg r)
    (A : ℝ) (hA : 0 ≤ A)
    (hT : ∀ s : ℕ, s ≤ N → ∀ x : M, tensor02CovDerivNormWith (I := I) s T g g x ≤ A)
    (x : M) :
    tensor02CovDerivNormWith (I := I) N T gRef gRef x ≤
      A * ((velTowerCoeffs (Module.finrank ℝ E) N Bmax Cg 1).slope *
          metricCovDerivNorm (I := I) N g gRef x +
        (velTowerCoeffs (Module.finrank ℝ E) N Bmax Cg 1).offset) := by
  set Q := (velTowerCoeffs (Module.finrank ℝ E) N Bmax Cg 1).slope *
      metricCovDerivNorm (I := I) N g gRef x +
    (velTowerCoeffs (Module.finrank ℝ E) N Bmax Cg 1).offset with hQ
  have hcoef := velCoeffs_nonneg (Module.finrank ℝ E) N Bmax Cg 1 hBmax1 zero_le_one
  have hQ0 : 0 ≤ Q := add_nonneg (mul_nonneg hcoef.1 (Real.sqrt_nonneg _)) hcoef.2
  have hεbound : ∀ ε : ℝ, 0 < ε →
      tensor02CovDerivNormWith (I := I) N T gRef gRef x ≤ (A + ε) * Q := by
    intro ε hε
    have hAε : 0 < A + ε := by linarith
    have hscale : ∀ (R : SmoothRiemannianMetric I M) (s : ℕ) (y : M),
        tensor02CovDerivNormWith (I := I) s ((A + ε)⁻¹ • T) R R y =
          (A + ε)⁻¹ * tensor02CovDerivNormWith (I := I) s T R R y := by
      intro R s y
      rw [tensor02CovDerivNormWith_smul, abs_of_pos (inv_pos.2 hAε)]
    have htow := velocity_tower_on (I := I) isOpen_univ gRef g ((A + ε)⁻¹ • T) N hN Bmax
      hBmax1 Cg 1 zero_le_one hequiv (fun r h1 h2 y _ => hBprev r h1 h2 y)
      (fun s hs y _ => by
        rw [← velNorm_eq_sqrt_iterCov, hscale]
        rw [inv_mul_le_iff₀ hAε, mul_one]
        exact (hT s hs y).trans (by linarith)) x (Set.mem_univ x)
    rw [← velNorm_eq_sqrt_iterCov, hscale, inv_mul_le_iff₀ hAε] at htow
    exact htow
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hε : 0 < δ / (Q + 1) := div_pos hδ (by linarith)
  have h1 := hεbound (δ / (Q + 1)) hε
  have h2 : δ / (Q + 1) * Q ≤ δ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  nlinarith

end CheegerGromovCompactness
end DifferentialGeometry
