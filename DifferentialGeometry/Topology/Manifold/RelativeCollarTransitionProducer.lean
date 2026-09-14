import DifferentialGeometry.Topology.Manifold.DoubleSeamTransport
import DifferentialGeometry.Topology.Manifold.InteriorChart
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Composition
import DifferentialGeometry.Topology.Diffeomorph.BoundaryFlow
import Mathlib.Geometry.Manifold.Diffeomorph

set_option autoImplicit false

noncomputable section

open Set Function Manifold Topology TopologicalSpace Bundle
open scoped ContDiff Topology Manifold

namespace DifferentialGeometry.Topology.Collar

private def prodSwapPartialDiffeomorph {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    PartialDiffeomorph (𝓘(ℝ, F).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ × F) (F × ℝ)
      (ℝ × F) ∞ where
  toFun := Prod.swap
  invFun := Prod.swap
  source := univ
  target := univ
  map_source' := fun _ _ => trivial
  map_target' := fun _ _ => trivial
  left_inv' := fun _ _ => rfl
  right_inv' := fun _ _ => rfl
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := by
    rw [contMDiffOn_prod_module_iff]
    constructor
    · change ContMDiffOn (𝓘(ℝ, F).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (Prod.snd : F × ℝ → ℝ) univ
      exact contMDiff_snd.contMDiffOn
    · change ContMDiffOn (𝓘(ℝ, F).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) ∞
        (Prod.fst : F × ℝ → F) univ
      exact contMDiff_fst.contMDiffOn
  contMDiffOn_invFun := by
    rw [contMDiffOn_prod_iff]
    constructor
    · rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
      exact contMDiff_snd.contMDiffOn
    · rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
      exact contMDiff_fst.contMDiffOn

private def partialDiffeomorphOfOpenPartialHomeomorph
    {E₁ H₁ M₁ E₂ H₂ M₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
    [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
    [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
    (I₁ : ModelWithCorners ℝ E₁ H₁) (I₂ : ModelWithCorners ℝ E₂ H₂)
    (e : OpenPartialHomeomorph M₁ M₂) (h₁ : ContMDiffOn I₁ I₂ ∞ e e.source)
    (h₂ : ContMDiffOn I₂ I₁ ∞ e.symm e.target) :
    PartialDiffeomorph I₁ I₂ M₁ M₂ ∞ where
  toPartialEquiv := e.toPartialEquiv
  open_source := e.open_source
  open_target := e.open_target
  contMDiffOn_toFun := h₁
  contMDiffOn_invFun := h₂

section ChartLemmas

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

@[simp]
theorem mfderiv_fst_self (w : ℝ × F) :
    mfderiv 𝓘(ℝ, ℝ × F) 𝓘(ℝ, ℝ) (Prod.fst : ℝ × F → ℝ) w =
      ContinuousLinearMap.fst ℝ ℝ F := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact mfderiv_fst

@[simp]
theorem mfderiv_snd_self (w : ℝ × F) :
    mfderiv 𝓘(ℝ, ℝ × F) 𝓘(ℝ, F) (Prod.snd : ℝ × F → F) w =
      ContinuousLinearMap.snd ℝ ℝ F := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact mfderiv_snd

theorem mdifferentiableAt_fst_self (w : ℝ × F) :
    MDifferentiableAt 𝓘(ℝ, ℝ × F) 𝓘(ℝ, ℝ) (Prod.fst : ℝ × F → ℝ) w := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact mdifferentiableAt_fst

theorem mdifferentiableAt_snd_self (w : ℝ × F) :
    MDifferentiableAt 𝓘(ℝ, ℝ × F) 𝓘(ℝ, F) (Prod.snd : ℝ × F → F) w := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact mdifferentiableAt_snd

omit [NormedSpace ℝ F] in
theorem frontier_prod_halfspace_self :
    frontier {z : ℝ × F | 0 ≤ z.1} = {z : ℝ × F | z.1 = 0} := by
  change frontier (Prod.fst ⁻¹' Ici (0 : ℝ)) = Prod.fst ⁻¹' {(0 : ℝ)}
  rw [← isOpenMap_fst.preimage_frontier_eq_frontier_preimage continuous_fst (Ici (0 : ℝ)),
    frontier_Ici]

end ChartLemmas

section CollarData

variable {M E H F G : Type*}
  [TopologicalSpace M] [CompactSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]
  {B : Set M} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
  [ChartedSpace G B] {J : ModelWithCorners ℝ F G} [IsManifold J ∞ B]
  [BoundarylessManifold J B]
  {r : C(M, ℝ)} {hr : ∀ b : B, r b.val = 0} {hz : ∀ x, r x = 0 → x ∈ B}
  {hn : ∀ x, 0 ≤ r x} {a : ℝ} {c : C(B × Icc (0 : ℝ) a, M)}
  {hheight : ∀ q, r (c q) = q.2.val} {hsmall : ∀ x, r x ≤ a → x ∈ range c}
  {hc : IsEmbedding c} {ha : 0 < a}
  [ChartedSpace E (Double B)] [IsManifold 𝓘(ℝ, E) ∞ (Double B)]
  {hseam : ∀ b : B, ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
    (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b) {q | |q.2| < a}}
  {hseamsymm : ∀ b : B, ContMDiffOn 𝓘(ℝ, E) (J.prod 𝓘(ℝ, ℝ)) ∞
    (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).symm
    {z | |doubleHeight B r hr z| < a}}
  {b : B}

private def seamPartialDiffeomorph
    (r : C(M, ℝ)) (hr : ∀ b : B, r b.val = 0)
    (hz : ∀ x, r x = 0 → x ∈ B) (hn : ∀ x, 0 ≤ r x)
    (c : C(B × Icc (0 : ℝ) a, M))
    (hheight : ∀ q, r (c q) = q.2.val) (hsmall : ∀ x, r x ≤ a → x ∈ range c)
    (hc : IsEmbedding c) (ha : 0 < a) (b : B)
    (hseam : ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b) {q | |q.2| < a})
    (hseamsymm : ContMDiffOn 𝓘(ℝ, E) (J.prod 𝓘(ℝ, ℝ)) ∞
      (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).symm
      {z | |doubleHeight B r hr z| < a}) :
    PartialDiffeomorph (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (B × ℝ) (Double B) ∞ :=
  partialDiffeomorphOfOpenPartialHomeomorph _ _
    (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b)
    (by rw [doubleSeamPatch_source]; exact hseam)
    (by rw [doubleSeamPatch_target]; exact hseamsymm)

private def chartPairPartialDiffeomorph (b : B) :
    PartialDiffeomorph (J.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, F).prod 𝓘(ℝ, ℝ)) (B × ℝ)
      (F × ℝ) ∞ :=
  DifferentialGeometry.Topology.PartialDiffeomorph.prod
    (DifferentialGeometry.Manifold.interiorChart J ∞ b)
    (DifferentialGeometry.PartialDiffeomorph.refl (I := 𝓘(ℝ, ℝ)) ℝ)

def boundarySeamChart
    (r : C(M, ℝ)) (hr : ∀ b : B, r b.val = 0)
    (hz : ∀ x, r x = 0 → x ∈ B) (hn : ∀ x, 0 ≤ r x)
    (c : C(B × Icc (0 : ℝ) a, M))
    (hheight : ∀ q, r (c q) = q.2.val) (hsmall : ∀ x, r x ≤ a → x ∈ range c)
    (hc : IsEmbedding c) (ha : 0 < a) (b b₁ : B)
    (hseam : ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b) {q | |q.2| < a})
    (hseamsymm : ContMDiffOn 𝓘(ℝ, E) (J.prod 𝓘(ℝ, ℝ)) ∞
      (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).symm
      {z | |doubleHeight B r hr z| < a}) :
    PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, ℝ × F) (Double B) (ℝ × F) ∞ :=
  _root_.PartialDiffeomorph.trans (I := 𝓘(ℝ, E)) (J := J.prod 𝓘(ℝ, ℝ))
    (K := 𝓘(ℝ, ℝ × F))
    (seamPartialDiffeomorph r hr hz hn c hheight hsmall hc ha b hseam hseamsymm).symm
    (_root_.PartialDiffeomorph.trans (I := J.prod 𝓘(ℝ, ℝ))
      (J := 𝓘(ℝ, F).prod 𝓘(ℝ, ℝ)) (K := 𝓘(ℝ, ℝ × F))
      (chartPairPartialDiffeomorph (F := F) b₁)
      (prodSwapPartialDiffeomorph (F := F)))

omit [BoundarylessManifold J B] [IsManifold 𝓘(ℝ, E) ∞ (Double B)] in
theorem boundarySeamChart_apply
    (r : C(M, ℝ)) (hr : ∀ b : B, r b.val = 0)
    (hz : ∀ x, r x = 0 → x ∈ B) (hn : ∀ x, 0 ≤ r x)
    (c : C(B × Icc (0 : ℝ) a, M))
    (hheight : ∀ q, r (c q) = q.2.val) (hsmall : ∀ x, r x ≤ a → x ∈ range c)
    (hc : IsEmbedding c) (ha : 0 < a) (b b₁ : B)
    (hseam : ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b) {q | |q.2| < a})
    (hseamsymm : ContMDiffOn 𝓘(ℝ, E) (J.prod 𝓘(ℝ, ℝ)) ∞
      (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).symm
      {z | |doubleHeight B r hr z| < a}) (z : Double B) :
    boundarySeamChart (F := F) r hr hz hn c hheight hsmall hc ha b b₁ hseam hseamsymm z =
      (((seamPartialDiffeomorph (E := E) (F := F) (G := G) (J := J) (B := B) (a := a)
          r hr hz hn c hheight hsmall hc ha b hseam hseamsymm).symm z).2,
        (DifferentialGeometry.Manifold.interiorChart J ∞ b₁)
          ((seamPartialDiffeomorph (E := E) (F := F) (G := G) (J := J) (B := B) (a := a)
          r hr hz hn c hheight hsmall hc ha b hseam hseamsymm).symm z).1) := rfl

omit [IsManifold J ∞ B] [BoundarylessManifold J B] [IsManifold 𝓘(ℝ, E) ∞ (Double B)] in
@[simp]
private theorem seamPartialDiffeomorph_apply
    (r : C(M, ℝ)) (hr : ∀ b : B, r b.val = 0)
    (hz : ∀ x, r x = 0 → x ∈ B) (hn : ∀ x, 0 ≤ r x)
    (c : C(B × Icc (0 : ℝ) a, M))
    (hheight : ∀ q, r (c q) = q.2.val) (hsmall : ∀ x, r x ≤ a → x ∈ range c)
    (hc : IsEmbedding c) (ha : 0 < a) (b : B)
    (hseam : ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b) {q | |q.2| < a})
    (hseamsymm : ContMDiffOn 𝓘(ℝ, E) (J.prod 𝓘(ℝ, ℝ)) ∞
      (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).symm
      {z | |doubleHeight B r hr z| < a}) (q : B × ℝ) :
    seamPartialDiffeomorph r hr hz hn c hheight hsmall hc ha b hseam hseamsymm q =
      doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b q := rfl

omit [IsManifold J ∞ B] [BoundarylessManifold J B] [IsManifold 𝓘(ℝ, E) ∞ (Double B)] in
@[simp]
private theorem seamPartialDiffeomorph_symm_apply
    (r : C(M, ℝ)) (hr : ∀ b : B, r b.val = 0)
    (hz : ∀ x, r x = 0 → x ∈ B) (hn : ∀ x, 0 ≤ r x)
    (c : C(B × Icc (0 : ℝ) a, M))
    (hheight : ∀ q, r (c q) = q.2.val) (hsmall : ∀ x, r x ≤ a → x ∈ range c)
    (hc : IsEmbedding c) (ha : 0 < a) (b : B)
    (hseam : ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b) {q | |q.2| < a})
    (hseamsymm : ContMDiffOn 𝓘(ℝ, E) (J.prod 𝓘(ℝ, ℝ)) ∞
      (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).symm
      {z | |doubleHeight B r hr z| < a}) (z : Double B) :
    (seamPartialDiffeomorph r hr hz hn c hheight hsmall hc ha b hseam hseamsymm).symm z =
      (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).symm z := rfl

omit [IsManifold J ∞ B] [BoundarylessManifold J B] [IsManifold 𝓘(ℝ, E) ∞ (Double B)] in
private theorem seamPartialDiffeomorph_source
    (r : C(M, ℝ)) (hr : ∀ b : B, r b.val = 0)
    (hz : ∀ x, r x = 0 → x ∈ B) (hn : ∀ x, 0 ≤ r x)
    (c : C(B × Icc (0 : ℝ) a, M))
    (hheight : ∀ q, r (c q) = q.2.val) (hsmall : ∀ x, r x ≤ a → x ∈ range c)
    (hc : IsEmbedding c) (ha : 0 < a) (b : B)
    (hseam : ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b) {q | |q.2| < a})
    (hseamsymm : ContMDiffOn 𝓘(ℝ, E) (J.prod 𝓘(ℝ, ℝ)) ∞
      (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).symm
      {z | |doubleHeight B r hr z| < a}) :
    (seamPartialDiffeomorph r hr hz hn c hheight hsmall hc ha b hseam hseamsymm).source =
      {q : B × ℝ | |q.2| < a} := by
  rw [show (seamPartialDiffeomorph r hr hz hn c hheight hsmall hc ha b hseam hseamsymm).source =
      (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).source from rfl,
    doubleSeamPatch_source]

omit [IsManifold J ∞ B] [BoundarylessManifold J B] [IsManifold 𝓘(ℝ, E) ∞ (Double B)] in
private theorem seamPartialDiffeomorph_target
    (r : C(M, ℝ)) (hr : ∀ b : B, r b.val = 0)
    (hz : ∀ x, r x = 0 → x ∈ B) (hn : ∀ x, 0 ≤ r x)
    (c : C(B × Icc (0 : ℝ) a, M))
    (hheight : ∀ q, r (c q) = q.2.val) (hsmall : ∀ x, r x ≤ a → x ∈ range c)
    (hc : IsEmbedding c) (ha : 0 < a) (b : B)
    (hseam : ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b) {q | |q.2| < a})
    (hseamsymm : ContMDiffOn 𝓘(ℝ, E) (J.prod 𝓘(ℝ, ℝ)) ∞
      (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).symm
      {z | |doubleHeight B r hr z| < a}) :
    (seamPartialDiffeomorph r hr hz hn c hheight hsmall hc ha b hseam hseamsymm).target =
      {z : Double B | |doubleHeight B r hr z| < a} := by
  rw [show (seamPartialDiffeomorph r hr hz hn c hheight hsmall hc ha b hseam hseamsymm).target =
      (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).target from rfl,
    doubleSeamPatch_target]

omit [BoundarylessManifold J B] [IsManifold 𝓘(ℝ, E) ∞ (Double B)] in
theorem boundarySeamChart_isImage
    (r : C(M, ℝ)) (hr : ∀ b : B, r b.val = 0)
    (hz : ∀ x, r x = 0 → x ∈ B) (hn : ∀ x, 0 ≤ r x)
    (c : C(B × Icc (0 : ℝ) a, M))
    (hheight : ∀ q, r (c q) = q.2.val) (hsmall : ∀ x, r x ≤ a → x ∈ range c)
    (hc : IsEmbedding c) (ha : 0 < a) (b b₁ : B)
    (hseam : ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b) {q | |q.2| < a})
    (hseamsymm : ContMDiffOn 𝓘(ℝ, E) (J.prod 𝓘(ℝ, ℝ)) ∞
      (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).symm
      {z | |doubleHeight B r hr z| < a}) :
    (boundarySeamChart (F := F) r hr hz hn c hheight hsmall hc ha b b₁ hseam
      hseamsymm).toOpenPartialHomeomorph.IsImage
      (range (doublePositive B)) {z : ℝ × F | 0 ≤ z.1} := by
  intro z hz'
  have hzt : z ∈ (seamPartialDiffeomorph r hr hz hn c hheight hsmall hc ha b
      hseam hseamsymm).target := hz'.1
  have hzt' : |doubleHeight B r hr z| < a := by
    rwa [seamPartialDiffeomorph_target r hr hz hn c hheight hsmall hc ha b hseam hseamsymm] at hzt
  have hq : |((seamPartialDiffeomorph r hr hz hn c hheight hsmall hc ha b
      hseam hseamsymm).symm z).2| < a := by
    have h := (seamPartialDiffeomorph r hr hz hn c hheight hsmall hc ha b
      hseam hseamsymm).map_target hzt
    rwa [seamPartialDiffeomorph_source r hr hz hn c hheight hsmall hc ha b
      hseam hseamsymm] at h
  rw [show (boundarySeamChart (F := F) r hr hz hn c hheight hsmall hc ha b b₁ hseam
        hseamsymm).toOpenPartialHomeomorph z =
      boundarySeamChart (F := F) r hr hz hn c hheight hsmall hc ha b b₁ hseam
        hseamsymm z from rfl,
    boundarySeamChart_apply]
  change 0 ≤ ((seamPartialDiffeomorph r hr hz hn c hheight hsmall hc ha b
      hseam hseamsymm).symm z).2 ↔ z ∈ range (doublePositive B)
  constructor
  · intro h0
    refine ⟨c (((seamPartialDiffeomorph r hr hz hn c hheight hsmall hc ha b
        hseam hseamsymm).symm z).1,
      ⟨((seamPartialDiffeomorph r hr hz hn c hheight hsmall hc ha b
        hseam hseamsymm).symm z).2, h0, (le_abs_self _).trans hq.le⟩), ?_⟩
    rw [← doubleSeamPatch_of_nonneg B r hr hz hn c hheight hsmall hc ha b hq h0,
      ← seamPartialDiffeomorph_apply r hr hz hn c hheight hsmall hc ha b hseam hseamsymm]
    exact (seamPartialDiffeomorph r hr hz hn c hheight hsmall hc ha b hseam hseamsymm).right_inv hzt
  · rintro ⟨y, rfl⟩
    rw [seamPartialDiffeomorph_symm_apply r hr hz hn c hheight hsmall hc ha b hseam hseamsymm,
      doubleSeamPatch_symm_height B r hr hz hn c hheight hsmall hc ha b hzt']
    exact hn y

omit [BoundarylessManifold J B] [IsManifold 𝓘(ℝ, E) ∞ (Double B)] in
@[simp]
theorem boundarySeamChart_apply_fst
    (r : C(M, ℝ)) (hr : ∀ b : B, r b.val = 0)
    (hz : ∀ x, r x = 0 → x ∈ B) (hn : ∀ x, 0 ≤ r x)
    (c : C(B × Icc (0 : ℝ) a, M))
    (hheight : ∀ q, r (c q) = q.2.val) (hsmall : ∀ x, r x ≤ a → x ∈ range c)
    (hc : IsEmbedding c) (ha : 0 < a) (b b₁ : B)
    (hseam : ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b) {q | |q.2| < a})
    (hseamsymm : ContMDiffOn 𝓘(ℝ, E) (J.prod 𝓘(ℝ, ℝ)) ∞
      (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).symm
      {z | |doubleHeight B r hr z| < a}) (z : Double B) :
    (boundarySeamChart (F := F) r hr hz hn c hheight hsmall hc ha b b₁ hseam hseamsymm z).1 =
      ((seamPartialDiffeomorph r hr hz hn c hheight hsmall hc ha b hseam hseamsymm).symm z).2 :=
  rfl

omit [BoundarylessManifold J B] [IsManifold 𝓘(ℝ, E) ∞ (Double B)] in
theorem boundarySeamChart_mfderiv_fst_eq_zero
    (r : C(M, ℝ)) (hr : ∀ b : B, r b.val = 0)
    (hz : ∀ x, r x = 0 → x ∈ B) (hn : ∀ x, 0 ≤ r x)
    (c : C(B × Icc (0 : ℝ) a, M))
    (hheight : ∀ q, r (c q) = q.2.val) (hsmall : ∀ x, r x ≤ a → x ∈ range c)
    (hc : IsEmbedding c) (ha : 0 < a) (b b₁ : B)
    (hseam : ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b) {q | |q.2| < a})
    (hseamsymm : ContMDiffOn 𝓘(ℝ, E) (J.prod 𝓘(ℝ, ℝ)) ∞
      (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).symm
      {z | |doubleHeight B r hr z| < a})
    (X : (z : Double B) → TangentSpace 𝓘(ℝ, E) z)
    (hXtan : ∀ q : B × ℝ, q.2 = 0 →
      ((mfderiv (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E)
          (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b) q).inverse
        (X (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b q))).2 = 0)
    {z : Double B}
    (hzsrc : z ∈ (boundarySeamChart (F := F) r hr hz hn c hheight hsmall hc ha b b₁
      hseam hseamsymm).source)
    (hzf : z ∈ frontier (range (doublePositive B))) :
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ × F)
      (boundarySeamChart (F := F) r hr hz hn c hheight hsmall hc ha b b₁ hseam hseamsymm) z
      (X z)).1 = 0 := by
  let e : PartialDiffeomorph (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (B × ℝ) (Double B) ∞ :=
    seamPartialDiffeomorph r hr hz hn c hheight hsmall hc ha b hseam hseamsymm
  let cc : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, ℝ × F) (Double B) (ℝ × F) ∞ :=
    boundarySeamChart (F := F) r hr hz hn c hheight hsmall hc ha b b₁ hseam hseamsymm
  have hzt : z ∈ e.target := hzsrc.1
  have hqsrc : e.symm z ∈ e.source := e.map_target hzt
  have hright : e (e.symm z) = z := e.right_inv hzt
  have hfst : (cc z).1 = 0 := by
    have h := (boundarySeamChart_isImage (F := F) r hr hz hn c hheight hsmall hc ha b b₁
      hseam hseamsymm).frontier hzsrc
    have h2 := h.mpr hzf
    rwa [frontier_prod_halfspace_self] at h2
  have hq0 : (e.symm z).2 = 0 := by
    have h := hfst
    rw [show cc z = ((e.symm z).2,
      (DifferentialGeometry.Manifold.interiorChart J ∞ b₁) (e.symm z).1) from rfl] at h
    exact h
  have hstep1 : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ × F) cc z (X z)).1 =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun w : Double B => (cc w).1) z (X z) := by
    have hmd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ × F) cc z :=
      cc.mdifferentiableAt (by norm_num) hzsrc
    have hcomp := mfderiv_comp_apply (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, ℝ × F))
      (I'' := 𝓘(ℝ, ℝ))
      (f := fun w : Double B => cc w) (g := (Prod.fst : ℝ × F → ℝ)) (x := z)
      (mdifferentiableAt_fst_self (F := F) (cc z)) hmd (X z)
    rw [mfderiv_fst_self] at hcomp
    exact hcomp.symm
  have hfun : (fun w : Double B => (cc w).1) = (fun w : Double B => (e.symm w).2) := by
    funext w
    exact boundarySeamChart_apply_fst r hr hz hn c hheight hsmall hc ha b b₁ hseam hseamsymm w
  have hstep2 : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun w : Double B => (cc w).1) z (X z) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun w : Double B => (e.symm w).2) z (X z) := by
    rw [hfun]
    rfl
  have hstep3 : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun w : Double B => (e.symm w).2) z (X z)
      = 0 := by
    rw [← hright]
    have hmd : MDifferentiableAt 𝓘(ℝ, E) (J.prod 𝓘(ℝ, ℝ)) (fun w : Double B => e.symm w)
        (e (e.symm z)) :=
      (e.contMDiffOn_invFun.contMDiffAt
        (e.open_target.mem_nhds (e.map_source hqsrc))).mdifferentiableAt (by norm_num)
    have hcomp := mfderiv_comp_apply (I := 𝓘(ℝ, E)) (I' := J.prod 𝓘(ℝ, ℝ))
      (I'' := 𝓘(ℝ, ℝ))
      (f := fun w : Double B => e.symm w) (g := (Prod.snd : B × ℝ → ℝ)) (x := e (e.symm z))
      mdifferentiableAt_snd hmd (X (e (e.symm z)))
    rw [mfderiv_snd] at hcomp
    rw [← DifferentialGeometry.VectorField.inverse_mfderiv_partialDiffeomorph e (by norm_num)
      hqsrc] at hcomp
    rw [show (fun w : Double B => (e.symm w).2) =
        (Prod.snd ∘ fun w : Double B => e.symm w) from rfl, hcomp]
    exact hXtan (e.symm z) hq0
  rw [hstep1, hstep2, hstep3]
  rfl

omit [CompactSpace M] [T2Space M] in
theorem doubleHeight_eq_zero_of_mem_frontier_doublePositive
    (r : C(M, ℝ)) (hr : ∀ b : B, r b.val = 0) (hn : ∀ x, 0 ≤ r x)
    {z : Double B} (hz : z ∈ frontier (range (doublePositive B))) :
    doubleHeight B r hr z = 0 := by
  have hle : ∀ w ∈ range (doublePositive B), 0 ≤ doubleHeight B r hr w := by
    rintro w ⟨x, rfl⟩
    simpa using hn x
  have hcl : closure (range (doublePositive B)) ⊆ {w | 0 ≤ doubleHeight B r hr w} :=
    closure_minimal hle (isClosed_le continuous_const (doubleHeight B r hr).continuous)
  have hpos : {w | 0 < doubleHeight B r hr w} ⊆ range (doublePositive B) := by
    intro w hw
    exact ⟨doubleFold B w, (doublePositivePatch B r hr hn).right_inv hw⟩
  have hcompl : z ∈ closure ((range (doublePositive B))ᶜ) := by
    rw [frontier_eq_closure_inter_closure] at hz
    exact hz.2
  have hcl' : closure ((range (doublePositive B))ᶜ) ⊆ {w | doubleHeight B r hr w ≤ 0} := by
    refine closure_minimal ?_ (isClosed_le (doubleHeight B r hr).continuous continuous_const)
    intro w hw
    by_contra hlt
    exact hw (hpos (by simpa using lt_of_not_ge hlt))
  exact le_antisymm (hcl' hcompl) (hcl (frontier_subset_closure hz))

omit [IsManifold 𝓘(ℝ, E) ∞ (Double B)] in
theorem exists_boundarySeamChart_of_frontier
    (r : C(M, ℝ)) (hr : ∀ b : B, r b.val = 0)
    (hz : ∀ x, r x = 0 → x ∈ B) (hn : ∀ x, 0 ≤ r x)
    (c : C(B × Icc (0 : ℝ) a, M))
    (hheight : ∀ q, r (c q) = q.2.val) (hsmall : ∀ x, r x ≤ a → x ∈ range c)
    (hc : IsEmbedding c) (ha : 0 < a) (b : B)
    (hseam : ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b) {q | |q.2| < a})
    (hseamsymm : ContMDiffOn 𝓘(ℝ, E) (J.prod 𝓘(ℝ, ℝ)) ∞
      (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).symm
      {z | |doubleHeight B r hr z| < a})
    (X : (z : Double B) → TangentSpace 𝓘(ℝ, E) z)
    (hXtan : ∀ q : B × ℝ, q.2 = 0 →
      ((mfderiv (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E)
          (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b) q).inverse
        (X (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b q))).2 = 0)
    {p : Double B} (hp : p ∈ frontier (range (doublePositive B))) :
    ∃ c' : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, ℝ × F) (Double B) (ℝ × F) ∞,
      p ∈ c'.source ∧
      c'.toOpenPartialHomeomorph.IsImage (range (doublePositive B)) {z : ℝ × F | 0 ≤ z.1} ∧
      ∀ x ∈ frontier (range (doublePositive B)) ∩ c'.source,
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ × F) c' x (X x)).1 = 0 := by
  let e : PartialDiffeomorph (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (B × ℝ) (Double B) ∞ :=
    seamPartialDiffeomorph r hr hz hn c hheight hsmall hc ha b hseam hseamsymm
  have hp0 : doubleHeight B r hr p = 0 :=
    doubleHeight_eq_zero_of_mem_frontier_doublePositive r hr hn hp
  have hpt : p ∈ e.target := by
    rw [seamPartialDiffeomorph_target r hr hz hn c hheight hsmall hc ha b hseam hseamsymm]
    change |doubleHeight B r hr p| < a
    rw [hp0]
    simpa using ha
  have hqsrc : e.symm p ∈ e.source := e.map_target hpt
  have hqchart : (e.symm p).1 ∈
      (DifferentialGeometry.Manifold.interiorChart J ∞ (e.symm p).1).source := by
    rw [DifferentialGeometry.Manifold.mem_interiorChart_source_iff]
    exact BoundarylessManifold.isInteriorPoint
  refine ⟨boundarySeamChart (F := F) r hr hz hn c hheight hsmall hc ha b (e.symm p).1
    hseam hseamsymm, ?_, ?_, ?_⟩
  · refine ⟨hpt, ?_⟩
    change e.symm p ∈ ((chartPairPartialDiffeomorph (F := F) (e.symm p).1).trans
      (prodSwapPartialDiffeomorph (F := F))).source
    rw [PartialDiffeomorph.trans_toPartialEquiv, OpenPartialHomeomorph.trans_source]
    refine ⟨?_, trivial⟩
    change e.symm p ∈
      (DifferentialGeometry.Manifold.interiorChart J ∞ (e.symm p).1).source ×ˢ univ
    exact ⟨hqchart, trivial⟩
  · exact boundarySeamChart_isImage (F := F) r hr hz hn c hheight hsmall hc ha b (e.symm p).1
      hseam hseamsymm
  · intro x hx
    exact boundarySeamChart_mfderiv_fst_eq_zero r hr hz hn c hheight hsmall hc ha b (e.symm p).1
      hseam hseamsymm X hXtan hx.2 hx.1

omit [IsManifold 𝓘(ℝ, E) ∞ (Double B)] in
theorem hcharts_of_doubleSeam
    (r : C(M, ℝ)) (hr : ∀ b : B, r b.val = 0)
    (hz : ∀ x, r x = 0 → x ∈ B) (hn : ∀ x, 0 ≤ r x)
    (c : C(B × Icc (0 : ℝ) a, M))
    (hheight : ∀ q, r (c q) = q.2.val) (hsmall : ∀ x, r x ≤ a → x ∈ range c)
    (hc : IsEmbedding c) (ha : 0 < a) (b : B)
    (hseam : ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b) {q | |q.2| < a})
    (hseamsymm : ContMDiffOn 𝓘(ℝ, E) (J.prod 𝓘(ℝ, ℝ)) ∞
      (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).symm
      {z | |doubleHeight B r hr z| < a})
    (X : (z : Double B) → TangentSpace 𝓘(ℝ, E) z)
    (hXtan : ∀ q : B × ℝ, q.2 = 0 →
      ((mfderiv (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E)
          (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b) q).inverse
        (X (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b q))).2 = 0) :
    ∀ p ∈ frontier (range (doublePositive B)), X p ≠ 0 →
      ∃ c' : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, ℝ × F) (Double B) (ℝ × F) ∞,
        p ∈ c'.source ∧
        c'.toOpenPartialHomeomorph.IsImage (range (doublePositive B)) {z : ℝ × F | 0 ≤ z.1} ∧
        ∀ x ∈ frontier (range (doublePositive B)) ∩ c'.source,
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ × F) c' x (X x)).1 = 0 :=
  fun _ hp _ =>
    exists_boundarySeamChart_of_frontier r hr hz hn c hheight hsmall hc ha b hseam hseamsymm
      X hXtan hp

theorem compactSupportFlow_mem_iff_of_doubleSeam
    (r : C(M, ℝ)) (hr : ∀ b : B, r b.val = 0)
    (hz : ∀ x, r x = 0 → x ∈ B) (hn : ∀ x, 0 ≤ r x)
    (c : C(B × Icc (0 : ℝ) a, M))
    (hheight : ∀ q, r (c q) = q.2.val) (hsmall : ∀ x, r x ≤ a → x ∈ range c)
    (hc : IsEmbedding c) (ha : 0 < a) (b : B)
    (hseam : ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b) {q | |q.2| < a})
    (hseamsymm : ContMDiffOn 𝓘(ℝ, E) (J.prod 𝓘(ℝ, ℝ)) ∞
      (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).symm
      {z | |doubleHeight B r hr z| < a})
    [T2Space (Double B)]
    [FiniteDimensional ℝ E]
    (X : (z : Double B) → TangentSpace 𝓘(ℝ, E) z)
    (hX : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
      (fun z => (⟨z, X z⟩ : TangentBundle 𝓘(ℝ, E) (Double B))))
    (hsupp : IsCompact (tsupport X))
    (hXtan : ∀ q : B × ℝ, q.2 = 0 →
      ((mfderiv (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E)
          (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b) q).inverse
        (X (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b q))).2 = 0) :
    let Φ := Diffeomorph.compactSupportFlow X hX hsupp
    ∀ (t : ℝ) (x : Double B),
      (Φ t x ∈ frontier (range (doublePositive B)) ↔
        x ∈ frontier (range (doublePositive B))) ∧
      (Φ t x ∈ range (doublePositive B) ↔ x ∈ range (doublePositive B)) ∧
      ((Φ t).symm x ∈ frontier (range (doublePositive B)) ↔
        x ∈ frontier (range (doublePositive B))) ∧
      ((Φ t).symm x ∈ range (doublePositive B) ↔ x ∈ range (doublePositive B)) := by
  refine Diffeomorph.compactSupportFlow_mem_iff_of_boundary_tangent (F := E) (E := F)
    X hX hsupp
    (range (doublePositive B)) ?_
  exact hcharts_of_doubleSeam r hr hz hn c hheight hsmall hc ha b hseam hseamsymm X hXtan

def doubleSeamFold
    (r : C(M, ℝ)) (hr : ∀ b : B, r b.val = 0)
    (hz : ∀ x, r x = 0 → x ∈ B) (hn : ∀ x, 0 ≤ r x)
    (c : C(B × Icc (0 : ℝ) a, M))
    (hheight : ∀ q, r (c q) = q.2.val) (hsmall : ∀ x, r x ≤ a → x ∈ range c)
    (hc : IsEmbedding c) (ha : 0 < a) (b : B) : B × ℝ → M :=
  fun q => doubleFold B (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b q)

def doubleSeamPullbackField
    (r : C(M, ℝ)) (hr : ∀ b : B, r b.val = 0)
    (hz : ∀ x, r x = 0 → x ∈ B) (hn : ∀ x, 0 ≤ r x)
    (c : C(B × Icc (0 : ℝ) a, M))
    (hheight : ∀ q, r (c q) = q.2.val) (hsmall : ∀ x, r x ≤ a → x ∈ range c)
    (hc : IsEmbedding c) (ha : 0 < a) (b : B)
    (V : ∀ x : M, TangentSpace I x) : (q : B × ℝ) → TangentSpace (J.prod 𝓘(ℝ, ℝ)) q :=
  fun q => (mfderiv (J.prod 𝓘(ℝ, ℝ)) I
      (doubleSeamFold r hr hz hn c hheight hsmall hc ha b) q).inverse
    (V (doubleSeamFold r hr hz hn c hheight hsmall hc ha b q))

theorem doubleSeamFold_apply_of_nonneg
    (r : C(M, ℝ)) (hr : ∀ b : B, r b.val = 0)
    (hz : ∀ x, r x = 0 → x ∈ B) (hn : ∀ x, 0 ≤ r x)
    (c : C(B × Icc (0 : ℝ) a, M))
    (hheight : ∀ q, r (c q) = q.2.val) (hsmall : ∀ x, r x ≤ a → x ∈ range c)
    (hc : IsEmbedding c) (ha : 0 < a) (b : B) {q : B × ℝ}
    (hq : q ∈ doublePositiveStrip B (a := a)) :
    r (doubleSeamFold r hr hz hn c hheight hsmall hc ha b q) = q.2 := by
  have hqa : |q.2| < a := by rw [abs_of_pos hq.1]; exact hq.2
  have hfold : doubleSeamFold r hr hz hn c hheight hsmall hc ha b q =
      c (q.1, ⟨q.2, hq.1.le, (le_abs_self q.2).trans hqa.le⟩) := by
    rw [doubleSeamFold,
      doubleSeamPatch_of_nonneg B r hr hz hn c hheight hsmall hc ha b hqa hq.1.le]
    rfl
  rw [hfold, hheight]

omit [IsManifold I ∞ M] [IsManifold J ∞ B] [BoundarylessManifold J B]
  [ChartedSpace E (Double B)] [IsManifold 𝓘(ℝ, E) ∞ (Double B)] in
theorem doubleSeamPullbackField_eq_zero_of_eq_zero
    (r : C(M, ℝ)) (hr : ∀ b : B, r b.val = 0)
    (hz : ∀ x, r x = 0 → x ∈ B) (hn : ∀ x, 0 ≤ r x)
    (c : C(B × Icc (0 : ℝ) a, M))
    (hheight : ∀ q, r (c q) = q.2.val) (hsmall : ∀ x, r x ≤ a → x ∈ range c)
    (hc : IsEmbedding c) (ha : 0 < a) (b : B)
    (V : ∀ x : M, TangentSpace I x) (hV : ∀ x : M, r x < a → V x = 0)
    {q : B × ℝ} (hq : q ∈ doublePositiveStrip B (a := a)) :
    doubleSeamPullbackField (J := J) (B := B) (F := F) r hr hz hn c hheight hsmall hc ha b V q
      = (0 : TangentSpace (J.prod 𝓘(ℝ, ℝ)) q) := by
  have hqr := doubleSeamFold_apply_of_nonneg r hr hz hn c hheight hsmall hc ha b hq
  rw [doubleSeamPullbackField, hV _ (by rw [hqr]; exact hq.2), map_zero]

def DoubleSeamFieldDatum
    (r : C(M, ℝ)) (hr : ∀ b : B, r b.val = 0)
    (hz : ∀ x, r x = 0 → x ∈ B) (hn : ∀ x, 0 ≤ r x)
    (c : C(B × Icc (0 : ℝ) a, M))
    (hheight : ∀ q, r (c q) = q.2.val) (hsmall : ∀ x, r x ≤ a → x ∈ range c)
    (hc : IsEmbedding c) (ha : 0 < a) (b : B)
    (V : ∀ x : M, TangentSpace I x) : Prop :=
  ∃ W : (q : B × ℝ) → TangentSpace (J.prod 𝓘(ℝ, ℝ)) q,
    ContMDiff (J.prod 𝓘(ℝ, ℝ)) (J.prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun q => (⟨q, W q⟩ : TangentBundle (J.prod 𝓘(ℝ, ℝ)) (B × ℝ))) ∧
    IsCompact (tsupport W) ∧
    (∀ q : B × ℝ, q.2 = 0 → (W q).2 = 0) ∧
    ∀ q ∈ doublePositiveStrip B (a := a),
      W q = doubleSeamPullbackField (J := J) (B := B) (F := F) r hr hz hn c hheight
        hsmall hc ha b V q

omit [IsManifold I ∞ M] [BoundarylessManifold J B] [ChartedSpace E (Double B)]
  [IsManifold 𝓘(ℝ, E) ∞ (Double B)] in
theorem doubleSeamFieldDatum_of_eq_zero_on_collar
    (r : C(M, ℝ)) (hr : ∀ b : B, r b.val = 0)
    (hz : ∀ x, r x = 0 → x ∈ B) (hn : ∀ x, 0 ≤ r x)
    (c : C(B × Icc (0 : ℝ) a, M))
    (hheight : ∀ q, r (c q) = q.2.val) (hsmall : ∀ x, r x ≤ a → x ∈ range c)
    (hc : IsEmbedding c) (ha : 0 < a) (b : B)
    (V : ∀ x : M, TangentSpace I x) (hV : ∀ x : M, r x < a → V x = 0) :
    DoubleSeamFieldDatum (J := J) (B := B) (F := F) r hr hz hn c hheight hsmall hc ha b V := by
  have hW : ContMDiff (J.prod 𝓘(ℝ, ℝ)) (J.prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun q : B × ℝ =>
        (⟨q, (0 : TangentSpace (J.prod 𝓘(ℝ, ℝ)) q)⟩ :
          TangentBundle (J.prod 𝓘(ℝ, ℝ)) (B × ℝ))) :=
    Bundle.contMDiff_zeroSection (𝕜 := ℝ) (IB := J.prod 𝓘(ℝ, ℝ))
      (F := F × ℝ) (E := fun x : B × ℝ => TangentSpace (J.prod 𝓘(ℝ, ℝ)) x)
  refine ⟨fun q => 0, hW, ?_, fun _ _ => rfl, ?_⟩
  · exact isCompact_empty.of_isClosed_subset (isClosed_tsupport _)
      ((IsClosed.closure_subset_iff isClosed_empty).mpr fun z hz' => hz' rfl)
  · intro q hq
    exact (doubleSeamPullbackField_eq_zero_of_eq_zero r hr hz hn c hheight hsmall hc ha b V hV
      hq).symm

end CollarData

end DifferentialGeometry.Topology.Collar
