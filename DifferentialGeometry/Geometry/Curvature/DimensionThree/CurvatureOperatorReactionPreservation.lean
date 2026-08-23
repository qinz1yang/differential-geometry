import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorReactionTensor
import DifferentialGeometry.Geometry.Curvature.DimensionThree.RicciControlsRm
import DifferentialGeometry.Geometry.Metric.InnerExpansion

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open Bundle DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]
variable {x : M}

theorem ricciFromSectional3_secRic3
    (l1 l2 l3 : Real) (i j : Fin 3) :
    DifferentialGeometry.Dim3Reaction.ricciFromSectional3
        (sec12Ric3 l1 l2 l3) (sec13Ric3 l1 l2 l3)
        (sec23Ric3 l1 l2 l3) i j =
      ricciDiag3 l1 l2 l3 i j := by
  fin_cases i <;> fin_cases j <;>
    simp [DifferentialGeometry.Dim3Reaction.ricciFromSectional3,
      sec12Ric3, sec13Ric3, sec23Ric3, ricciDiag3] <;> ring

theorem stdRmDiag3_neg_eq_rm_ricciFromSectional3
    (l1 l2 l3 : Real) (i j k l : Fin 3) :
    stdRmDiag3 (-l1) (-l2) (-l3) i j k l =
      DifferentialGeometry.Dim3Reaction.rm
        (DifferentialGeometry.Dim3Reaction.ricciFromSectional3
          (sec12Ric3 l1 l2 l3) (sec13Ric3 l1 l2 l3)
          (sec23Ric3 l1 l2 l3)) i j k l := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [stdRmDiag3, ricciDiag3, ricciEigenScalar3, delta3,
      DifferentialGeometry.Dim3Reaction.rm,
      DifferentialGeometry.Dim3Reaction.ricciFromSectional3,
      DifferentialGeometry.Dim3Reaction.sc, DifferentialGeometry.Dim3Reaction.kd,
      sec12Ric3, sec13Ric3, sec23Ric3] <;> ring

theorem algebraicCurvatureOperatorNonnegative_normalForm3
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02At (I := I) (M := M) x)
    (scalar : Real)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (hsymm : RicciSymAt (I := I) Ric)
    (htrace : ∀ basis : Module.Basis (Fin 3) Real (TangentSpace I x),
      OrthonormalBasisAt (I := I) g x basis →
        RiemannFromRicci3DTraceDataAt (I := I) g (-Ric) (-scalar)
          (A : Tensor04At (I := I) (M := M) x) basis)
    (hA : A ∈ algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    ∃ (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
        (K12 K13 K23 : Real),
      OrthonormalBasisAt (I := I) g x basis ∧
        0 ≤ K12 ∧ 0 ≤ K13 ∧ 0 ≤ K23 ∧
        (∀ i j,
          ricciCompAt (I := I) basis Ric i j =
            DifferentialGeometry.Dim3Reaction.ricciFromSectional3 K12 K13 K23 i j) ∧
        ∀ a b c d,
          tensor04StdAt (I := I) (M := M)
            (A : Tensor04At (I := I) (M := M) x)
            (basis a) (basis b) (basis c) (basis d) =
              DifferentialGeometry.Dim3Reaction.rm
                (DifferentialGeometry.Dim3Reaction.ricciFromSectional3 K12 K13 K23)
                a b c d := by
  obtain ⟨basis, l1, l2, l3, horth, hdiag⟩ :=
    ricciEigen3 (I := I) g Ric hdim hsymm
  let K12 := sec12Ric3 l1 l2 l3
  let K13 := sec13Ric3 l1 l2 l3
  let K23 := sec23Ric3 l1 l2 l3
  have htraceBasis := htrace basis horth
  have h00 :
      stdRicci3 (standardRmCompAt (I := I) basis
        (A : Tensor04At (I := I) (M := M) x)) 0 0 = -l1 := by
    rw [← htraceBasis.ricci_trace 0 0]
    rw [ricciCompAt_apply]
    change -(Ric (vec2 (I := I) (basis 0) (basis 0))) = -l1
    have h := hdiag.2 0 0
    rw [ricciCompAt_apply] at h
    simpa [ricciDiag3] using congrArg Neg.neg h
  have h11 :
      stdRicci3 (standardRmCompAt (I := I) basis
        (A : Tensor04At (I := I) (M := M) x)) 1 1 = -l2 := by
    rw [← htraceBasis.ricci_trace 1 1]
    rw [ricciCompAt_apply]
    change -(Ric (vec2 (I := I) (basis 1) (basis 1))) = -l2
    have h := hdiag.2 1 1
    rw [ricciCompAt_apply] at h
    simpa [ricciDiag3] using congrArg Neg.neg h
  have h22 :
      stdRicci3 (standardRmCompAt (I := I) basis
        (A : Tensor04At (I := I) (M := M) x)) 2 2 = -l3 := by
    rw [← htraceBasis.ricci_trace 2 2]
    rw [ricciCompAt_apply]
    change -(Ric (vec2 (I := I) (basis 2) (basis 2))) = -l3
    have h := hdiag.2 2 2
    rw [ricciCompAt_apply] at h
    simpa [ricciDiag3] using congrArg Neg.neg h
  have hscalar : scalar = ricciEigenScalar3 l1 l2 l3 := by
    have hs := htraceBasis.scalar_trace
    unfold stdScalar3 at hs
    simp [h00, h11, h22] at hs
    unfold ricciEigenScalar3
    linarith
  have hdiagNeg :
      RicciDiagAt (I := I) (-Ric) (-scalar) (-l1) (-l2) (-l3) basis := by
    constructor
    · unfold ricciEigenScalar3 at hscalar ⊢
      linarith
    · intro i j
      have hij := hdiag.2 i j
      rw [ricciCompAt_apply] at hij ⊢
      change -(Ric (vec2 (I := I) (basis i) (basis j))) =
        ricciDiag3 (-l1) (-l2) (-l3) i j
      rw [hij]
      fin_cases i <;> fin_cases j <;> simp [ricciDiag3]
  have hcompStd := stdRmComp_eq_diag (I := I) htraceBasis hdiagNeg
  have hcomp : ∀ a b c d,
      tensor04StdAt (I := I) (M := M)
        (A : Tensor04At (I := I) (M := M) x)
        (basis a) (basis b) (basis c) (basis d) =
          DifferentialGeometry.Dim3Reaction.rm
            (DifferentialGeometry.Dim3Reaction.ricciFromSectional3 K12 K13 K23)
            a b c d := by
    intro a b c d
    unfold tensor04StdAt
    rw [← rm04CompAt_apply]
    change standardRmCompAt (I := I) basis
      (A : Tensor04At (I := I) (M := M) x) a b c d = _
    rw [hcompStd a b c d]
    exact stdRmDiag3_neg_eq_rm_ricciFromSectional3 l1 l2 l3 a b c d
  have hsectional :
      A ∈ algebraicSectionalNonnegativeCone (I := I) (M := M) :=
    algebraicCurvatureOperatorNonnegativeCone_le_sectionalNonnegativeCone hA
  have h12 := mem_algebraicSectionalNonnegativeCone.mp hsectional (basis 0) (basis 1)
  have h13 := mem_algebraicSectionalNonnegativeCone.mp hsectional (basis 0) (basis 2)
  have h23 := mem_algebraicSectionalNonnegativeCone.mp hsectional (basis 1) (basis 2)
  change 0 ≤ tensor04StdAt (I := I) (M := M)
    (A : Tensor04At (I := I) (M := M) x) (basis 0) (basis 1) (basis 1) (basis 0) at h12
  change 0 ≤ tensor04StdAt (I := I) (M := M)
    (A : Tensor04At (I := I) (M := M) x) (basis 0) (basis 2) (basis 2) (basis 0) at h13
  change 0 ≤ tensor04StdAt (I := I) (M := M)
    (A : Tensor04At (I := I) (M := M) x) (basis 1) (basis 2) (basis 2) (basis 1) at h23
  rw [hcomp 0 1 1 0] at h12
  rw [hcomp 0 2 2 0] at h13
  rw [hcomp 1 2 2 1] at h23
  have hK12 : 0 ≤ K12 := by
    simp [DifferentialGeometry.Dim3Reaction.rm,
      DifferentialGeometry.Dim3Reaction.ricciFromSectional3,
      DifferentialGeometry.Dim3Reaction.sc, DifferentialGeometry.Dim3Reaction.kd] at h12
    linarith
  have hK13 : 0 ≤ K13 := by
    simp [DifferentialGeometry.Dim3Reaction.rm,
      DifferentialGeometry.Dim3Reaction.ricciFromSectional3,
      DifferentialGeometry.Dim3Reaction.sc, DifferentialGeometry.Dim3Reaction.kd] at h13
    linarith
  have hK23 : 0 ≤ K23 := by
    simp [DifferentialGeometry.Dim3Reaction.rm,
      DifferentialGeometry.Dim3Reaction.ricciFromSectional3,
      DifferentialGeometry.Dim3Reaction.sc, DifferentialGeometry.Dim3Reaction.kd] at h23
    linarith
  refine ⟨basis, K12, K13, K23, horth, hK12, hK13, hK23, ?_, hcomp⟩
  intro i j
  rw [hdiag.2 i j]
  exact (ricciFromSectional3_secRic3 l1 l2 l3 i j).symm

theorem algebraicCurvatureOperatorReaction_nonnegative3
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02At (I := I) (M := M) x)
    (scalar : Real)
    (A Q : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (hsymm : RicciSymAt (I := I) Ric)
    (htrace : ∀ basis : Module.Basis (Fin 3) Real (TangentSpace I x),
      OrthonormalBasisAt (I := I) g x basis →
        RiemannFromRicci3DTraceDataAt (I := I) g (-Ric) (-scalar)
          (A : Tensor04At (I := I) (M := M) x) basis)
    (hA : A ∈ algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hreaction : ∀ (basis : Module.Basis (Fin 3) Real (TangentSpace I x)),
      OrthonormalBasisAt (I := I) g x basis → ∀ a b c d,
        tensor04StdAt (I := I) (M := M)
          (Q : Tensor04At (I := I) (M := M) x)
          (basis a) (basis b) (basis c) (basis d) =
            -2 * DifferentialGeometry.Dim3Reaction.Bsharp
              (fun i j ↦ ricciCompAt (I := I) basis Ric i j) a b c d) :
    Q ∈ algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) := by
  obtain ⟨basis, K12, K13, K23, horth, h12, h13, h23, hRic, _⟩ :=
    algebraicCurvatureOperatorNonnegative_normalForm3
      (I := I) g Ric scalar A hdim hsymm htrace hA
  apply algebraicCurvatureOperatorNonnegative_of_components_eq_reaction
    basis Q K12 K13 K23 h12 h13 h23
  intro a b c d
  rw [hreaction basis horth a b c d]
  unfold DifferentialGeometry.Dim3Reaction.curvatureTensorReaction3
  congr 2
  funext i j
  exact hRic i j

omit [FiniteDimensional ℝ E] in
lemma ricci_quad_sum_repr
    (Ric : Tensor02At (I := I) (M := M) x)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (v : TangentSpace I x) :
    Ric (vec2 v v) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        (basis.repr v i) * (basis.repr v j) * Ric (vec2 (basis i) (basis j)) := by
  classical
  let c : Fin 3 → ℝ := fun i => basis.repr v i
  have hsum : v = ∑ i : Fin 3, c i • basis i := by
    simp [c, basis.sum_repr]
  change Ric (vec2 v v) = ∑ i : Fin 3, ∑ j : Fin 3, c i * c j * Ric (vec2 (basis i) (basis j))
  rw [hsum]
  have hvec : vec2 (∑ i : Fin 3, c i • basis i) (∑ i : Fin 3, c i • basis i) =
      fun _ : Fin 2 => ∑ i : Fin 3, c i • basis i := by
    funext i
    fin_cases i <;> simp [vec2]
  rw [hvec]
  change Ric (fun _ : Fin 2 => ∑ i : Fin 3, c i • basis i) =
      ∑ i : Fin 3, ∑ j : Fin 3, c i * c j * Ric (vec2 (basis i) (basis j))
  trans ∑ r : Fin 2 → Fin 3, (c (r 0) * c (r 1)) • Ric (vec2 (basis (r 0)) (basis (r 1)))
  · have hmap := ContinuousMultilinearMap.map_sum (f := Ric)
      (g := fun _ : Fin 2 => fun i : Fin 3 => c i • basis i)
    calc
      Ric (fun _ : Fin 2 => ∑ i : Fin 3, c i • basis i)
          = ∑ r : Fin 2 → Fin 3, Ric (fun i : Fin 2 => c (r i) • basis (r i)) := hmap
      _ = ∑ r : Fin 2 → Fin 3, (c (r 0) * c (r 1)) • Ric (vec2 (basis (r 0)) (basis (r 1))) := by
        apply Finset.sum_congr rfl
        intro r hr
        have hsmul := ContinuousMultilinearMap.map_smul_univ (f := Ric)
          (c := fun i : Fin 2 => c (r i)) (m := fun i : Fin 2 => basis (r i))
        calc
          Ric (fun i : Fin 2 => c (r i) • basis (r i))
              = (∏ i : Fin 2, c (r i)) • Ric (fun i : Fin 2 => basis (r i)) := hsmul
          _ = (c (r 0) * c (r 1)) • Ric (fun i : Fin 2 => basis (r i)) := by
            rw [Fin.prod_univ_two]
          _ = (c (r 0) * c (r 1)) • Ric (vec2 (basis (r 0)) (basis (r 1))) := by
            have hfun : (fun i : Fin 2 => basis (r i)) = vec2 (basis (r 0)) (basis (r 1)) := by
              funext i
              fin_cases i <;> simp [vec2]
            rw [hfun]
  · trans ∑ p : Fin 3 × Fin 3, c p.1 * c p.2 * Ric (vec2 (basis p.1) (basis p.2))
    · apply Finset.sum_bij (fun (r : Fin 2 → Fin 3) (_ : r ∈ Finset.univ) => (r 0, r 1))
      · intro r hr
        simp
      · intro a₁ ha₁ a₂ ha₂ h
        have h0 : a₁ 0 = a₂ 0 := congrArg (fun p : Fin 3 × Fin 3 => p.1) h
        have h1 : a₁ 1 = a₂ 1 := congrArg (fun p : Fin 3 × Fin 3 => p.2) h
        funext i
        fin_cases i
        · exact h0
        · exact h1
      · intro b hb
        refine ⟨![b.1, b.2], by simp, ?_⟩
        simp
      · intro r hr
        simp
    · rw [← Fintype.sum_prod_type']

theorem algebraicCurvatureOperatorNonnegative_iff_ricci_upper_bound3
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02At (I := I) (M := M) x)
    (scalar : Real)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (hsymm : RicciSymAt (I := I) Ric)
    (htrace : ∀ basis : Module.Basis (Fin 3) Real (TangentSpace I x),
      OrthonormalBasisAt (I := I) g x basis →
        RiemannFromRicci3DTraceDataAt (I := I) g (-Ric) (-scalar)
          (A : Tensor04At (I := I) (M := M) x) basis) :
    A ∈ algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) ↔
      (∀ v : TangentSpace I x, Ric (vec2 (I := I) v v) ≤ (scalar / 2) * g.inner x v v) := by
  constructor
  · intro hA
    obtain ⟨basis, K12, K13, K23, horth, hK12, hK13, hK23, hRic, hcomp⟩ :=
      algebraicCurvatureOperatorNonnegative_normalForm3 (I := I) g Ric scalar A hdim hsymm htrace hA
    let lam : Fin 3 → Real := fun i =>
      DifferentialGeometry.Dim3Reaction.ricciFromSectional3 K12 K13 K23 i i
    have hscalar : scalar = lam 0 + lam 1 + lam 2 := by
      have htr := htrace basis horth
      have hs := htr.scalar_trace
      have hdiag0 : stdRicci3 (standardRmCompAt (I := I) basis
          (A : Tensor04At (I := I) (M := M) x)) 0 0 = -lam 0 := by
        rw [← htr.ricci_trace 0 0]
        simpa [ricciCompAt, lam] using hRic 0 0
      have hdiag1 : stdRicci3 (standardRmCompAt (I := I) basis
          (A : Tensor04At (I := I) (M := M) x)) 1 1 = -lam 1 := by
        rw [← htr.ricci_trace 1 1]
        simpa [ricciCompAt, lam] using hRic 1 1
      have hdiag2 : stdRicci3 (standardRmCompAt (I := I) basis
          (A : Tensor04At (I := I) (M := M) x)) 2 2 = -lam 2 := by
        rw [← htr.ricci_trace 2 2]
        simpa [ricciCompAt, lam] using hRic 2 2
      unfold stdScalar3 at hs
      simp [hdiag0, hdiag1, hdiag2] at hs
      have : scalar = lam 0 + lam 1 + lam 2 := by linarith
      simpa [ricciEigenScalar3] using this
    have hsc : scalar = 2 * (K12 + K13 + K23) := by
      rw [hscalar]
      simp [lam, DifferentialGeometry.Dim3Reaction.ricciFromSectional3]
      ring
    have hlam_le : ∀ i : Fin 3, lam i ≤ scalar / 2 := by
      intro i
      fin_cases i
      · dsimp [lam]
        rw [hsc]
        simp [DifferentialGeometry.Dim3Reaction.ricciFromSectional3]
        nlinarith [hK23]
      · dsimp [lam]
        rw [hsc]
        simp [DifferentialGeometry.Dim3Reaction.ricciFromSectional3]
        nlinarith [hK13]
      · dsimp [lam]
        rw [hsc]
        simp [DifferentialGeometry.Dim3Reaction.ricciFromSectional3]
        nlinarith [hK12]
    intro v
    let c : Fin 3 → ℝ := fun i => basis.repr v i
    have hdiag : ∀ i j, Ric (vec2 (basis i) (basis j)) = if i = j then lam i else 0 := by
      intro i j
      rw [← ricciCompAt_apply]
      rw [hRic i j]
      simp [lam, DifferentialGeometry.Dim3Reaction.ricciFromSectional3]
    have hExp := ricci_quad_sum_repr (I := I) (M := M) Ric basis v
    have hcollapse : (∑ i : Fin 3, ∑ j : Fin 3,
        c i * c j * Ric (vec2 (basis i) (basis j))) = ∑ i : Fin 3, (c i)^2 * lam i := by
      simp_rw [hdiag]
      simp [pow_two]
    have hg : g.inner x v v = ∑ i : Fin 3, (basis.repr v i)^2 := by
      conv_lhs => rw [show v = ∑ i : Fin 3, c i • basis i from by simp [c, basis.sum_repr]]
      have hon : ∀ i j, g.inner x (basis i) (basis j) = if i = j then (1 : ℝ) else 0 := by
        intro i j
        exact horth i j
      exact DifferentialGeometry.Geometry.Riemannian.inner_sum_orthonormal g x basis hon c
    have hmain : Ric (vec2 v v) ≤ (scalar / 2) * g.inner x v v := by
      rw [hExp, hcollapse, hg]
      calc
        (∑ i : Fin 3, (c i)^2 * lam i) ≤ (∑ i : Fin 3, (c i)^2 * (scalar / 2)) := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_left (hlam_le i) (sq_nonneg _)
        _ = (scalar / 2) * (∑ i : Fin 3, (c i)^2) := by
          rw [Finset.mul_sum]
          congr 1
          funext i
          ring
    exact hmain
  · intro hRicBound
    obtain ⟨basis, l1, l2, l3, horth, hdiag⟩ := ricciEigen3 (I := I) g Ric hdim hsymm
    let K12 : ℝ := sec12Ric3 l1 l2 l3
    let K13 : ℝ := sec13Ric3 l1 l2 l3
    let K23 : ℝ := sec23Ric3 l1 l2 l3
    have htr := htrace basis horth
    have hscalar' : scalar = l1 + l2 + l3 := by
      have hs := htr.scalar_trace
      have hr0 : stdRicci3 (standardRmCompAt (I := I) basis
          (A : Tensor04At (I := I) (M := M) x)) 0 0 = -l1 := by
        rw [← htr.ricci_trace 0 0]
        rw [show ricciCompAt (I := I) basis (-Ric) 0 0 =
            -ricciCompAt (I := I) basis Ric 0 0 by simp [ricciCompAt]]
        rw [hdiag.2 0 0]
        simp [ricciDiag3]
      have hr1 : stdRicci3 (standardRmCompAt (I := I) basis
          (A : Tensor04At (I := I) (M := M) x)) 1 1 = -l2 := by
        rw [← htr.ricci_trace 1 1]
        rw [show ricciCompAt (I := I) basis (-Ric) 1 1 =
            -ricciCompAt (I := I) basis Ric 1 1 by simp [ricciCompAt]]
        rw [hdiag.2 1 1]
        simp [ricciDiag3]
      have hr2 : stdRicci3 (standardRmCompAt (I := I) basis
          (A : Tensor04At (I := I) (M := M) x)) 2 2 = -l3 := by
        rw [← htr.ricci_trace 2 2]
        rw [show ricciCompAt (I := I) basis (-Ric) 2 2 =
            -ricciCompAt (I := I) basis Ric 2 2 by simp [ricciCompAt]]
        rw [hdiag.2 2 2]
        simp [ricciDiag3]
      unfold stdScalar3 at hs
      simp [hr0, hr1, hr2] at hs
      linarith
    have hl1 : l1 ≤ scalar / 2 := by
      have h := hRicBound (basis 0)
      rw [← ricciCompAt_apply, hdiag.2 0 0, horth 0 0] at h
      simpa [ricciDiag3, delta3] using h
    have hl2 : l2 ≤ scalar / 2 := by
      have h := hRicBound (basis 1)
      rw [← ricciCompAt_apply, hdiag.2 1 1, horth 1 1] at h
      simpa [ricciDiag3, delta3] using h
    have hl3 : l3 ≤ scalar / 2 := by
      have h := hRicBound (basis 2)
      rw [← ricciCompAt_apply, hdiag.2 2 2, horth 2 2] at h
      simpa [ricciDiag3, delta3] using h
    have hK12' : 0 ≤ K12 := by
      dsimp [K12, sec12Ric3]
      have hsc2 : (l1 + l2 + l3) / 2 = scalar / 2 := by rw [hscalar']
      nlinarith [hl3, hsc2]
    have hK13' : 0 ≤ K13 := by
      dsimp [K13, sec13Ric3]
      have hsc2 : (l1 + l2 + l3) / 2 = scalar / 2 := by rw [hscalar']
      nlinarith [hl2, hsc2]
    have hK23' : 0 ≤ K23 := by
      dsimp [K23, sec23Ric3]
      have hsc2 : (l1 + l2 + l3) / 2 = scalar / 2 := by rw [hscalar']
      nlinarith [hl1, hsc2]
    let R : Fin 3 → Fin 3 → ℝ := fun i j =>
      DifferentialGeometry.Dim3Reaction.ricciFromSectional3 K12 K13 K23 i j
    have hstdR : ∀ i j, stdRicci3 (standardRmCompAt (I := I) basis
          (A : Tensor04At (I := I) (M := M) x)) i j = -R i j := by
      intro i j
      rw [← htr.ricci_trace i j]
      rw [show ricciCompAt (I := I) basis (-Ric) i j =
          -ricciCompAt (I := I) basis Ric i j by simp [ricciCompAt]]
      rw [hdiag.2 i j]
      fin_cases i <;> fin_cases j <;>
        simp [R, ricciDiag3, K12, K13, K23, sec12Ric3, sec13Ric3, sec23Ric3,
          DifferentialGeometry.Dim3Reaction.ricciFromSectional3] <;> ring
    have hstdS : stdScalar3 (standardRmCompAt (I := I) basis
          (A : Tensor04At (I := I) (M := M) x)) = -scalar := htr.scalar_trace.symm
    have hscR : scalar = DifferentialGeometry.Dim3Reaction.sc R := by
      dsimp [DifferentialGeometry.Dim3Reaction.sc, R]
      rw [hscalar']
      simp [K12, K13, K23, sec12Ric3, sec13Ric3, sec23Ric3,
        DifferentialGeometry.Dim3Reaction.ricciFromSectional3]
      ring
    have hcomp : ∀ a b c d,
        tensor04StdAt (I := I) (M := M)
          (A : Tensor04At (I := I) (M := M) x)
          (basis a) (basis b) (basis c) (basis d) =
            DifferentialGeometry.Dim3Reaction.rm R a b c d := by
      intro a b c d
      have hformula := rm04Comp_displayedRiemannFromRicci3D_at_of_curvature_symmetries
        (Rm04 := (A : Tensor04At (I := I) (M := M) x)) htr.curvature_symmetries a b d c
      rw [show tensor04StdAt (I := I) (M := M)
            (A : Tensor04At (I := I) (M := M) x)
            (basis a) (basis b) (basis c) (basis d) =
            (A : Tensor04At (I := I) (M := M) x)
              (vec4 (basis a) (basis b) (basis c) (basis d)) by rfl,
        ← rm04CompAt_apply]
      rw [hformula]
      simp only [hstdR, hstdS, hscR]
      dsimp [R]
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
        simp [DifferentialGeometry.Dim3Reaction.rm,
          DifferentialGeometry.Dim3Reaction.sc,
          DifferentialGeometry.Dim3Reaction.kd, delta3] <;> ring
    exact algebraicCurvatureOperatorNonnegative_of_components_eq_rm basis A K12 K13 K23
      hK12' hK13' hK23' (by intro a b c d; simpa [R] using hcomp a b c d)

theorem curvatureOperatorUpperBoundReaction_null_nonneg3
    (l1 l2 l3 : ℝ)
    (hT2 : 0 ≤ (l1 + l2 + l3) / 2 - l2)
    (hT3 : 0 ≤ (l1 + l2 + l3) / 2 - l3)
    (hnull : (l1 + l2 + l3) / 2 = l1) :
    0 ≤ (l1^2 + l2^2 + l3^2) - (l1 + l2 + l3) * l1 -
      2 * (sec12Ric3 l1 l2 l3 * l2 + sec13Ric3 l1 l2 l3 * l3) + 2 * l1^2 := by
  have hsum : l1 = l2 + l3 := by nlinarith
  have hl2 : 0 ≤ l2 := by
    have h : 0 ≤ (l1 + l2 + l3) / 2 - l3 := hT3
    rw [hsum] at h
    field_simp at h
    linarith
  have hl3 : 0 ≤ l3 := by
    have h : 0 ≤ (l1 + l2 + l3) / 2 - l2 := hT2
    rw [hsum] at h
    field_simp at h
    linarith
  have hreaction : (l1^2 + l2^2 + l3^2) - (l1 + l2 + l3) * l1 -
      2 * (sec12Ric3 l1 l2 l3 * l2 + sec13Ric3 l1 l2 l3 * l3) + 2 * l1^2 =
    2 * l2 * l3 := by
    dsimp [sec12Ric3, sec13Ric3]
    nlinarith [hsum]
  rw [hreaction]
  exact mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hl2) hl3
end DifferentialGeometry.Geometry.Curvature
