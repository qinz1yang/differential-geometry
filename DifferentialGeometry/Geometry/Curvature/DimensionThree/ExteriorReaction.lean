import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ExteriorRepresentation
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorNormalization
import DifferentialGeometry.Geometry.Curvature.QuadraticTensor

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

open scoped BigOperators RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem orthonormal_bivector_family (b : OrthonormalBasis (Fin 3) ℝ E) :
    Orthonormal ℝ (fun i : Fin 3 => exteriorPower.ιMulti ℝ 2
      ![b (bivectorIndex3 i).1, b (bivectorIndex3 i).2]) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [exteriorPower.inner_ιMulti_ιMulti, Matrix.det_fin_two]
  fin_cases i <;> fin_cases j <;>
    simp [bivectorIndex3, b.inner_eq_ite]

def curvatureBivectorBasis (b : OrthonormalBasis (Fin 3) ℝ E) :
    OrthonormalBasis (Fin 3) ℝ (⋀[ℝ]^2 E) :=
  OrthonormalBasis.mk (orthonormal_bivector_family b)
    ((orthonormal_bivector_family b).linearIndependent.span_eq_top_of_card_eq_finrank (by
      rw [exteriorPower.finrank_eq, Module.finrank_eq_card_basis b.toBasis]
      norm_num)).ge

@[simp] theorem curvatureBivectorBasis_apply (b : OrthonormalBasis (Fin 3) ℝ E) (i : Fin 3) :
    curvatureBivectorBasis b i = exteriorPower.ιMulti ℝ 2
      ![b (bivectorIndex3 i).1, b (bivectorIndex3 i).2] := by
  exact congrFun (OrthonormalBasis.coe_mk _ _) i

private def bivectorOrderEmbedding (i : Fin 3) : Fin 2 ↪o Fin 3 :=
  OrderEmbedding.ofStrictMono ![(bivectorIndex3 i).1, (bivectorIndex3 i).2]
    (by
      intro a c h
      fin_cases a <;> fin_cases c <;> norm_num at h
      fin_cases i <;> decide)

def curvatureBivectorIndexEquiv : Fin 3 ≃ Set.powersetCard (Fin 3) 2 :=
  Equiv.ofBijective (fun i => Set.powersetCard.ofFinEmbEquiv (bivectorOrderEmbedding i)) (by
    apply (Fintype.bijective_iff_injective_and_card _).2
    refine ⟨?_, ?_⟩
    · intro i j h
      have he := Set.powersetCard.ofFinEmbEquiv.injective h
      have h0 := congrArg (fun f : Fin 2 ↪o Fin 3 => f 0) he
      have h1 := congrArg (fun f : Fin 2 ↪o Fin 3 => f 1) he
      change (bivectorIndex3 i).1 = (bivectorIndex3 j).1 at h0
      change (bivectorIndex3 i).2 = (bivectorIndex3 j).2 at h1
      fin_cases i <;> fin_cases j <;> simp_all [bivectorIndex3]
    · rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, Set.powersetCard.card]
      norm_num)

theorem curvatureBivectorBasis_eq_exteriorPower_reindex
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis (Fin 3) ℝ E) :
    curvatureBivectorBasis b = (b.exteriorPower 2).reindex curvatureBivectorIndexEquiv.symm := by
  apply DFunLike.ext
  intro i
  rw [OrthonormalBasis.reindex_apply, curvatureBivectorBasis_apply]
  change _ = (b.exteriorPower 2).toBasis _
  rw [OrthonormalBasis.toBasis_exteriorPower, exteriorPower.basis_apply]
  simp only [exteriorPower.ιMulti_family, curvatureBivectorIndexEquiv,
    Equiv.ofBijective_apply, Equiv.symm_symm, Equiv.symm_apply_apply]
  congr 1
  ext q
  fin_cases q <;> rfl

theorem traceNormalizedCurvatureEndomorphism_toMatrix
    (b : OrthonormalBasis (Fin 3) ℝ E)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (hT : IsAlgCurvForm (fun x y z w => T ![x, y, z, w])) :
    LinearMap.toMatrix (curvatureBivectorBasis b).toBasis (curvatureBivectorBasis b).toBasis
      (exteriorPower.traceNormalizedCurvatureEndomorphism T hT).toLinearMap =
      fun i j => 2 * T ![b (bivectorIndex3 i).1, b (bivectorIndex3 i).2,
        b (bivectorIndex3 j).2, b (bivectorIndex3 j).1] := by
  ext i j
  rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis,
    real_inner_comm, curvatureBivectorBasis_apply, curvatureBivectorBasis_apply]
  change ⟪exteriorPower.traceNormalizedCurvatureEndomorphism T hT
    (exteriorPower.ιMulti ℝ 2 ![b (bivectorIndex3 j).1, b (bivectorIndex3 j).2]),
    exteriorPower.ιMulti ℝ 2 ![b (bivectorIndex3 i).1, b (bivectorIndex3 i).2]⟫ = _
  rw [exteriorPower.inner_traceNormalizedCurvatureEndomorphism_ιMulti]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hT.pair_swap (b (bivectorIndex3 j).1) (b (bivectorIndex3 j).2)
    (b (bivectorIndex3 i).2) (b (bivectorIndex3 i).1)]
  have ha := hT.anti_first (b (bivectorIndex3 i).2) (b (bivectorIndex3 i).1)
    (b (bivectorIndex3 j).1) (b (bivectorIndex3 j).2)
  have hb := hT.anti_last (b (bivectorIndex3 i).1) (b (bivectorIndex3 i).2)
    (b (bivectorIndex3 j).1) (b (bivectorIndex3 j).2)
  linarith

theorem curvatureOperatorReactionEndomorphism3_traceNormalizedCurvatureEndomorphism_toMatrix
    (b : OrthonormalBasis (Fin 3) ℝ E)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (hT : IsAlgCurvForm (fun x y z w => T ![x, y, z, w])) :
    LinearMap.toMatrix (curvatureBivectorBasis b).toBasis (curvatureBivectorBasis b).toBasis
      (curvatureOperatorReactionEndomorphism3
        (exteriorPower.traceNormalizedCurvatureEndomorphism T hT).toLinearMap) =
      curvatureOperatorReaction3 (fun i j =>
        2 * T ![b (bivectorIndex3 i).1, b (bivectorIndex3 i).2,
          b (bivectorIndex3 j).2, b (bivectorIndex3 j).1]) := by
  rw [curvatureOperatorReactionEndomorphism3_toMatrix, traceNormalizedCurvatureEndomorphism_toMatrix]

theorem curvatureOperatorReactionEndomorphism3_traceNormalizedCurvatureEndomorphism_apply_eq_negative_b_comp
    (b : OrthonormalBasis (Fin 3) ℝ E)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (hT : IsAlgCurvForm (fun x y z w => T ![x, y, z, w])) (i j : Fin 3) :
    LinearMap.toMatrix (curvatureBivectorBasis b).toBasis (curvatureBivectorBasis b).toBasis
        (curvatureOperatorReactionEndomorphism3
          (exteriorPower.traceNormalizedCurvatureEndomorphism T hT).toLinearMap) i j =
      let R := fun a c d e : Fin 3 => T ![b a, b c, b d, b e]
      let a := (bivectorIndex3 i).1
      let c := (bivectorIndex3 i).2
      let d := (bivectorIndex3 j).2
      let e := (bivectorIndex3 j).1
      4 * ((-PDE.RicciFlow.bComp delta3 R a c d e) -
        (-PDE.RicciFlow.bComp delta3 R a c e d) +
        (-PDE.RicciFlow.bComp delta3 R a d c e) -
        (-PDE.RicciFlow.bComp delta3 R a e c d)) := by
  let R := fun a c d e : Fin 3 => T ![b a, b c, b d, b e]
  have hR : AlgebraicCurvatureSymmetries3 R := by
    refine ⟨?_, ?_, ?_⟩
    · intro a c d e
      exact hT.anti_first (b c) (b a) (b d) (b e)
    · intro a c d e
      exact hT.anti_last (b a) (b c) (b e) (b d)
    · intro a c d e
      exact hT.pair_swap (b d) (b e) (b a) (b c)
  rw [curvatureOperatorReactionEndomorphism3_traceNormalizedCurvatureEndomorphism_toMatrix]
  exact curvatureOperatorReaction3_apply_eq_negative_b_comp R hR i j


omit [FiniteDimensional ℝ E] in
private theorem wedge_swap (x y : E) :
    exteriorPower.ιMulti ℝ 2 ![y, x] = -exteriorPower.ιMulti ℝ 2 ![x, y] := by
  have h : (![x, y] : Fin 2 → E) ∘ Equiv.swap 0 1 = ![y, x] := by
    ext i
    fin_cases i <;> simp
  simpa only [h] using (exteriorPower.ιMulti ℝ 2).map_swap ![x, y] (by decide : (0 : Fin 2) ≠ 1)

private theorem inner_reaction_curvatureBivectorBasis
    (b : OrthonormalBasis (Fin 3) ℝ E)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (hT : IsAlgCurvForm (fun x y z w => T ![x, y, z, w])) (i j : Fin 3) :
    ⟪curvatureOperatorReactionEndomorphism3
        (exteriorPower.traceNormalizedCurvatureEndomorphism T hT).toLinearMap
        (curvatureBivectorBasis b i), curvatureBivectorBasis b j⟫ =
      let R := fun a c d e : Fin 3 => T ![b a, b c, b d, b e]
      let a := (bivectorIndex3 i).1
      let c := (bivectorIndex3 i).2
      let d := (bivectorIndex3 j).1
      let e := (bivectorIndex3 j).2
      4 * (PDE.RicciFlow.bComp delta3 R a c d e -
        PDE.RicciFlow.bComp delta3 R a c e d +
        PDE.RicciFlow.bComp delta3 R a d c e -
        PDE.RicciFlow.bComp delta3 R a e c d) := by
  have h := curvatureOperatorReactionEndomorphism3_traceNormalizedCurvatureEndomorphism_apply_eq_negative_b_comp
    b T hT i j
  rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis] at h
  have hs := curvatureOperatorReactionEndomorphism3_isSymmetric _
    (exteriorPower.traceNormalizedCurvatureEndomorphism_isSymmetric T hT)
  rw [← hs] at h
  dsimp only at h ⊢
  linarith

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem alternating_pairs_ext
    (F G : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hF1 : ∀ a c d e, F a c d e = -F c a d e)
    (hF2 : ∀ a c d e, F a c d e = -F a c e d)
    (hG1 : ∀ a c d e, G a c d e = -G c a d e)
    (hG2 : ∀ a c d e, G a c d e = -G a c e d)
    (h : ∀ i j, F (bivectorIndex3 i).1 (bivectorIndex3 i).2
      (bivectorIndex3 j).1 (bivectorIndex3 j).2 =
        G (bivectorIndex3 i).1 (bivectorIndex3 i).2
          (bivectorIndex3 j).1 (bivectorIndex3 j).2) (a c d e : Fin 3) :
    F a c d e = G a c d e := by
  have hp (a c : Fin 3) (hac : a < c) : ∃ i, bivectorIndex3 i = (a, c) := by
    fin_cases a <;> fin_cases c <;> norm_num at hac
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  have hord (a c d e : Fin 3) (hac : a < c) (hde : d < e) : F a c d e = G a c d e := by
    obtain ⟨i, hi⟩ := hp a c hac
    obtain ⟨j, hj⟩ := hp d e hde
    simpa only [hi, hj] using h i j
  have hfirst (a c d e : Fin 3) (hac : a < c) : F a c d e = G a c d e := by
    rcases lt_trichotomy d e with hd | hd | hd
    · exact hord a c d e hac hd
    · subst e
      have hf := hF2 a c d d
      have hg := hG2 a c d d
      linarith
    · rw [hF2, hG2, hord a c e d hac hd]
  rcases lt_trichotomy a c with ha | ha | ha
  · exact hfirst a c d e ha
  · subst c
    have hf := hF1 a a d e
    have hg := hG1 a a d e
    linarith
  · rw [hF1, hG1, hfirst c a d e ha]

theorem endomorphismTensor_curvatureOperatorReactionEndomorphism3_basis
    (b : OrthonormalBasis (Fin 3) ℝ E)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (hT : IsAlgCurvForm (fun x y z w => T ![x, y, z, w])) (a c d e : Fin 3) :
    exteriorPower.endomorphismTensor 2
        (curvatureOperatorReactionEndomorphism3
          (exteriorPower.traceNormalizedCurvatureEndomorphism T hT).toLinearMap).toContinuousLinearMap
        ![b a, b c, b d, b e] =
      let R := fun a c d e : Fin 3 => T ![b a, b c, b d, b e]
      4 * (PDE.RicciFlow.bComp delta3 R a c d e -
        PDE.RicciFlow.bComp delta3 R a c e d +
        PDE.RicciFlow.bComp delta3 R a d c e -
        PDE.RicciFlow.bComp delta3 R a e c d) := by
  let R := fun a c d e : Fin 3 => T ![b a, b c, b d, b e]
  have hR : PDE.RicciFlow.Rm04Symm R :=
    ⟨fun a c d e => hT.anti_first _ _ _ _, fun a c d e => hT.anti_last _ _ _ _,
      fun a c d e => hT.pair_swap _ _ _ _, fun a c d e => hT.bianchi _ _ _ _⟩
  let B := PDE.RicciFlow.bComp delta3 R
  have hswap (a c d e : Fin 3) : B a c d e = B c a e d :=
    PDE.RicciFlow.bComp_swap delta3 hR a c d e
  have hpair (a c d e : Fin 3) : B a c d e = B d e a c := by
    simp [B, PDE.RicciFlow.bComp, delta3, mul_comm]
  let Q := fun a c d e => 4 * (B a c d e - B a c e d + B a d c e - B a e c d)
  have hQ1 (a c d e : Fin 3) : Q a c d e = -Q c a d e := by
    dsimp only [Q]
    rw [hswap c a d e, hswap c a e d]
    rw [hpair c d a e, hpair c e a d]
    ring
  have hQ2 (a c d e : Fin 3) : Q a c d e = -Q a c e d := by
    dsimp only [Q]
    ring
  let L := curvatureOperatorReactionEndomorphism3
    (exteriorPower.traceNormalizedCurvatureEndomorphism T hT).toLinearMap
  let F := fun a c d e => ⟪L (exteriorPower.ιMulti ℝ 2 ![b a, b c]),
    exteriorPower.ιMulti ℝ 2 ![b d, b e]⟫
  have hF1 (a c d e : Fin 3) : F a c d e = -F c a d e := by
    dsimp only [F]
    rw [wedge_swap (b c) (b a), map_neg, inner_neg_left]
  have hF2 (a c d e : Fin 3) : F a c d e = -F a c e d := by
    dsimp only [F]
    rw [wedge_swap (b e) (b d), inner_neg_right]
  have hi (i j : Fin 3) : F (bivectorIndex3 i).1 (bivectorIndex3 i).2
      (bivectorIndex3 j).1 (bivectorIndex3 j).2 =
        Q (bivectorIndex3 i).1 (bivectorIndex3 i).2
          (bivectorIndex3 j).1 (bivectorIndex3 j).2 := by
    simpa only [curvatureBivectorBasis_apply] using inner_reaction_curvatureBivectorBasis b T hT i j
  have hvec : (![b a, b c, b d, b e] : Fin 4 → E) = Fin.append ![b a, b c] ![b d, b e] := by
    ext q
    fin_cases q <;> rfl
  rw [hvec, exteriorPower.endomorphismTensor_apply_append]
  exact alternating_pairs_ext F Q hF1 hF2 hQ1 hQ2 hi a c d e

end DifferentialGeometry.Geometry.Curvature.DimensionThree

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

open Bundle
open PDE.RicciFlow
open Tensor0SBundle
open scoped Manifold ContDiff BigOperators RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem endomorphismTensor_curvatureOperatorReactionEndomorphism3_pullback
    (g : SmoothRiemannianMetric I M) (x : M)
    (ι : F ≃L[ℝ] TangentSpace I x)
    (hι : ∀ v w, g.inner x (ι v) (ι w) = ⟪v, w⟫)
    (hdim : Module.finrank ℝ F = 3)
    (A : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) 4)
    (hA : IsAlgCurvForm (fun a c d e : F => A x ![ι a, ι c, ι d, ι e])) :
    exteriorPower.endomorphismTensor 2
      (curvatureOperatorReactionEndomorphism3
        (exteriorPower.traceNormalizedCurvatureEndomorphism
          ((A x).compContinuousLinearMap (fun _ => ι.toContinuousLinearMap))
          (by
            convert hA using 1
            ext a c d e
            change A x (fun q => ι (![a, c, d, e] q)) = _
            congr 1
            ext q
            fin_cases q <;> rfl)).toLinearMap
        ).toContinuousLinearMap =
      (4 : ℝ) • (curvatureQuadraticCombination g A x).compContinuousLinearMap
        (fun _ => ι.toContinuousLinearMap) := by
  let b := (stdOrthonormalBasis ℝ F).reindex (finCongr hdim)
  let T := (A x).compContinuousLinearMap (fun _ => ι.toContinuousLinearMap)
  have hT : IsAlgCurvForm (fun a c d e : F => T ![a, c, d, e]) := by
    convert hA using 1
    ext a c d e
    change A x (fun q => ι (![a, c, d, e] q)) = _
    congr 1
    ext q
    fin_cases q <;> rfl
  apply (Tensor.Multilinear.continuousMultilinearMapBasis b.toBasis 4).repr.injective
  ext m
  rw [Tensor.Multilinear.continuousMultilinearMap_basis_repr,
    Tensor.Multilinear.continuousMultilinearMap_basis_repr]
  have hvec : (fun q : Fin 4 => b (m q)) = ![b (m 0), b (m 1), b (m 2), b (m 3)] := by
    ext q
    fin_cases q <;> rfl
  simp only [OrthonormalBasis.coe_toBasis, hvec, smul_apply, smul_eq_mul]
  have hl := endomorphismTensor_curvatureOperatorReactionEndomorphism3_basis
    b T hT (m 0) (m 1) (m 2) (m 3)
  have hinv : ∀ i j,
      (∑ k, delta3 i k * ⟪b k, b j⟫) = (if i = j then 1 else 0) ∧
      (∑ k, ⟪b i, b k⟫ * delta3 k j) = (if i = j then 1 else 0) := by
    intro i j
    simp [delta3, b.inner_eq_ite]
  have hr := curvatureQuadraticCombination_apply_isometry_basis g x ι
    (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ) hι b.toBasis delta3 hinv A m
  simp only [OrthonormalBasis.coe_toBasis] at hr
  have heval : ((curvatureQuadraticCombination g A x).compContinuousLinearMap
      (fun _ => ι.toContinuousLinearMap)) ![b (m 0), b (m 1), b (m 2), b (m 3)] =
      curvatureQuadraticCombination g A x (fun q => ι (b (m q))) := by
    change curvatureQuadraticCombination g A x (fun q =>
      ι (![b (m 0), b (m 1), b (m 2), b (m 3)] q)) = _
    congr 1
    ext q
    fin_cases q <;> rfl
  rw [heval, hr]
  have hR : (fun a c d e : Fin 3 => T ![b a, b c, b d, b e]) =
      (fun a c d e : Fin 3 => A x (vec4 (ι (b a)) (ι (b c)) (ι (b d)) (ι (b e)))) := by
    funext a c d e
    change A x (fun q => ι (![b a, b c, b d, b e] q)) = _
    congr 1
    ext q
    fin_cases q <;> rfl
  dsimp only at hl
  rw [hR] at hl
  exact hl

end DifferentialGeometry.Geometry.Curvature.DimensionThree
