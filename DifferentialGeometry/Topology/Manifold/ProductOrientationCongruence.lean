import DifferentialGeometry.Topology.Manifold.ProductOrientation

set_option autoImplicit false
noncomputable section
open Manifold Module
open scoped Manifold ContDiff
namespace DifferentialGeometry

noncomputable def basisOfOrientation {E : Type*} [AddCommGroup E] [Module ℝ E]
    (fd : FiniteDimensional ℝ E) {m : ℕ} (h : Nonempty (Fin m))
    (o : Orientation ℝ E (Fin m)) (hm : Fintype.card (Fin m) = Module.finrank ℝ E) :
    {b : Basis (Fin m) ℝ E // b.orientation = o} := by
  letI := fd
  letI := h
  exact ⟨o.someBasis hm, o.someBasis_orientation hm⟩

theorem orientation_map_trans_fin {A B C : Type*} [AddCommGroup A] [Module ℝ A]
    [AddCommGroup B] [Module ℝ B] [AddCommGroup C] [Module ℝ C] {m : ℕ}
    (e : A ≃ₗ[ℝ] B) (f : B ≃ₗ[ℝ] C) (o : Orientation ℝ A (Fin m)) :
    Orientation.map (Fin m) (e.trans f) o =
      Orientation.map (Fin m) f (Orientation.map (Fin m) e o) := by
  induction o using Module.Ray.ind with | h v hv => rfl

theorem orientation_map_refl_apply {M : Type*} [AddCommGroup M] [Module ℝ M] {k : ℕ}
    (o : Orientation ℝ M (Fin k)) : Orientation.map (Fin k) (LinearEquiv.refl ℝ M) o = o := by
  rw [Orientation.map_refl]
  rfl

theorem tangentProdEquiv_eq_refl {E F H H' M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    [TopologicalSpace H'] {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
    (p : M × N) : tangentProdEquiv I J p = LinearEquiv.refl ℝ (E × F) := rfl

theorem tangentProdEquiv_apply_eq_self {E F H H' M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    [TopologicalSpace H'] {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
    (p : M × N) (v : TangentSpace (I.prod J) p) : tangentProdEquiv I J p v = v := by
  rw [tangentProdEquiv_eq_refl]
  rfl

theorem tangentProdEquiv_symm_eq_refl {E F H H' M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    [TopologicalSpace H'] {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
    (p : M × N) : (tangentProdEquiv I J p).symm = LinearEquiv.refl ℝ (E × F) := rfl

theorem tangentProdEquiv_symm_apply_eq_self {E F H H' M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    [TopologicalSpace H'] {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
    (p : M × N) (v : TangentSpace I p.1 × TangentSpace J p.2) :
    (tangentProdEquiv I J p).symm v = v := by
  rw [tangentProdEquiv_symm_eq_refl]
  rfl

theorem orientation_map_tangentProdEquiv_symm {E F H H' M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace H'] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ F H'} [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace H' N] (p : M × N) {k : ℕ}
    (o : Orientation ℝ (E × F) (Fin k)) :
    Orientation.map (Fin k) (tangentProdEquiv I J p).symm o = o := by
  rw [tangentProdEquiv_symm_eq_refl]
  exact orientation_map_refl_apply o

theorem orientation_map_tangentProdEquiv {E F H H' M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace H'] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ F H'} [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace H' N] (p : M × N) {k : ℕ}
    (o : Orientation ℝ (E × F) (Fin k)) :
    Orientation.map (Fin k) (tangentProdEquiv I J p) o = o := by
  rw [tangentProdEquiv_eq_refl]
  exact orientation_map_refl_apply o

theorem prodCongr_sumElim {E F E' F' : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup E'] [Module ℝ E']
    [AddCommGroup F] [Module ℝ F] [AddCommGroup F'] [Module ℝ F']
    {ι ι' : Type*} (A : E ≃ₗ[ℝ] E') (B : F ≃ₗ[ℝ] F') (f : ι → E) (g : ι' → F)
    (j : ι ⊕ ι') :
    (A.prodCongr B) (Sum.elim (LinearMap.inl ℝ E F ∘ f) (LinearMap.inr ℝ E F ∘ g) j) =
      Sum.elim (LinearMap.inl ℝ E' F' ∘ (A ∘ f))
        (LinearMap.inr ℝ E' F' ∘ (B ∘ g)) j := by
  cases j <;> simp [LinearEquiv.prodCongr_apply]

theorem prodBasis_reindex_map {E F E' F' : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup E'] [Module ℝ E']
    [AddCommGroup F] [Module ℝ F] [AddCommGroup F'] [Module ℝ F']
    {m n : ℕ} (b : Basis (Fin m) ℝ E) (c : Basis (Fin n) ℝ F)
    (A : E ≃ₗ[ℝ] E') (B : F ≃ₗ[ℝ] F') :
    (((b.prod c).reindex finSumFinEquiv).map (A.prodCongr B)) =
      (((b.map A).prod (c.map B)).reindex finSumFinEquiv) := by
  ext i
  · simp only [Basis.map_apply, Basis.reindex_apply, Basis.prod_apply]
    exact congrArg Prod.fst (prodCongr_sumElim A B b c (finSumFinEquiv.symm i))
  · simp only [Basis.map_apply, Basis.reindex_apply, Basis.prod_apply]
    exact congrArg Prod.snd (prodCongr_sumElim A B b c (finSumFinEquiv.symm i))

theorem productTangentBasis_orientation_eq {E F H H' M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    [TopologicalSpace H'] {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
    {m n : ℕ} {x : M} {y : N}
    (b : Basis (Fin m) ℝ (TangentSpace I x)) (c : Basis (Fin n) ℝ (TangentSpace J y)) :
    (productTangentBasis I J b c).orientation
      = (((b.prod c).reindex finSumFinEquiv)).orientation := by
  rw [productTangentBasis, Basis.orientation_map]
  exact orientation_map_tangentProdEquiv_symm (I := I) (J := J) (x, y) _

theorem productTangentBasis_orientation_neg {E F H H' M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    [TopologicalSpace H'] {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
    {m n : ℕ} {x : M} {y : N}
    (b : Basis (Fin m) ℝ (TangentSpace I x)) (c : Basis (Fin n) ℝ (TangentSpace J y))
    (i : Fin m) :
    (productTangentBasis I J (b.unitsSMul (Function.update 1 i (-1))) c).orientation
      = -(productTangentBasis I J b c).orientation := by
  have hbp : (b.unitsSMul (Function.update 1 i (-1))).prod c
      = (b.prod c).unitsSMul (Function.update 1 (Sum.inl i) (-1)) := by
    ext j <;> cases j <;>
      simp only [Basis.unitsSMul_apply, Basis.prod_apply, Function.update_apply,
        Sum.elim_inl, Sum.elim_inr] <;>
      (split_ifs <;> simp_all [Basis.unitsSMul_apply, Units.smul_def])
  rw [productTangentBasis_orientation_eq, productTangentBasis_orientation_eq, hbp,
    Basis.orientation_reindex, Basis.orientation_reindex, Basis.orientation_neg_single,
    Orientation.reindex_neg]
  rfl

theorem productOrientation_opposite {E F H H' M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    [TopologicalSpace H'] {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [IsManifold I ∞ M] [IsManifold J ∞ N] {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (oM : ManifoldOrientation I M m) (oN : ManifoldOrientation J N n) :
    (productOrientation I J hm hn oM oN).opposite
      = productOrientation I J hm hn oM.opposite oN := by
  refine productOrientation_unique I J hm hn oM.opposite oN
    (productOrientation I J hm hn oM oN).opposite ?_
  intro x y b c hb hc
  have hb1 : (b.unitsSMul (Function.update 1 (⟨0, hm⟩ : Fin m) (-1))).orientation
      = oM.orientation x := by
    rw [Basis.orientation_neg_single, hb, ManifoldOrientation.opposite_orientation]
    exact neg_neg (oM.orientation x)
  have hchar := productOrientation_characterization I J hm hn oM oN x y
    (b.unitsSMul (Function.update 1 (⟨0, hm⟩ : Fin m) (-1))) c hb1 hc
  have hneg := productTangentBasis_orientation_neg (I := I) (J := J) b c (⟨0, hm⟩ : Fin m)
  rw [ManifoldOrientation.opposite_orientation, ← hchar, hneg]
  exact (neg_neg ((productTangentBasis I J b c).orientation)).symm

theorem productTangentBasis_orientation_map {E E' F F' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {H H' H'' H''' : Type*} [TopologicalSpace H] [TopologicalSpace H'']
    [TopologicalSpace H'] [TopologicalSpace H'''] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ F H'} {I' : ModelWithCorners ℝ E' H''}
    {J' : ModelWithCorners ℝ F' H'''} {M M' N N' : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [TopologicalSpace M'] [ChartedSpace H'' M'] [TopologicalSpace N]
    [ChartedSpace H' N] [TopologicalSpace N'] [ChartedSpace H''' N']
    {m n : ℕ} {x : M} {y : N} {x' : M'} {y' : N'}
    (b : Basis (Fin m) ℝ (TangentSpace I x)) (c : Basis (Fin n) ℝ (TangentSpace J y))
    (A : TangentSpace I x ≃ₗ[ℝ] TangentSpace I' x')
    (B : TangentSpace J y ≃ₗ[ℝ] TangentSpace J' y') :
    Orientation.map (Fin (m + n)) (A.prodCongr B) ((productTangentBasis I J b c).orientation) =
      (productTangentBasis I' J' (b.map A) (c.map B)).orientation := by
  have hL : (productTangentBasis I J b c).orientation
      = (((b.prod c).reindex finSumFinEquiv)).orientation :=
    productTangentBasis_orientation_eq b c
  have hR : (productTangentBasis I' J' (b.map A) (c.map B)).orientation
      = (((b.map A).prod (c.map B)).reindex finSumFinEquiv).orientation :=
    productTangentBasis_orientation_eq (b.map A) (c.map B)
  rw [hL, hR, ← Basis.orientation_map ((b.prod c).reindex finSumFinEquiv) (A.prodCongr B),
    prodBasis_reindex_map b c A B]

set_option backward.isDefEq.respectTransparency false in
theorem Diffeomorph.prodCongr_preservesOrientation
    {E E' F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H H' H'' H''' : Type*} [TopologicalSpace H] [TopologicalSpace H'']
    [TopologicalSpace H'] [TopologicalSpace H'''] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ F H'} {I' : ModelWithCorners ℝ E' H''}
    {J' : ModelWithCorners ℝ F H'''} {M M' N N' : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [TopologicalSpace M'] [ChartedSpace H'' M'] [TopologicalSpace N]
    [ChartedSpace H' N] [TopologicalSpace N'] [ChartedSpace H''' N']
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ E']
    [IsManifold I ∞ M] [IsManifold J ∞ N] [IsManifold I' ∞ M'] [IsManifold J' ∞ N']
    {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    {oM : ManifoldOrientation I M m} {oN : ManifoldOrientation J N n}
    {oM' : ManifoldOrientation I' M' m} {oN' : ManifoldOrientation J' N' n}
    (f : M ≃ₘ⟮I, I'⟯ M') (g : N ≃ₘ⟮J, J'⟯ N')
    (hf : f.preservesOrientation oM oM') (hg : g.preservesOrientation oN oN') :
    (f.prodCongr g : (M × N) ≃ₘ⟮I.prod J, I'.prod J'⟯ (M' × N')).preservesOrientation
      (productOrientation I J hm hn oM oN) (productOrientation I' J' hm hn oM' oN') := by
  intro p
  obtain ⟨x, y⟩ := p
  have hcardM : Fintype.card (Fin m) = Module.finrank ℝ (TangentSpace I x) := by
    rw [Fintype.card_fin]
    exact oM.dimension_eq.symm
  have hcardN : Fintype.card (Fin n) = Module.finrank ℝ (TangentSpace J y) := by
    rw [Fintype.card_fin]
    exact oN.dimension_eq.symm
  let bd := basisOfOrientation (E := E) (fd := inferInstance)
    (⟨⟨0, hm⟩⟩ : Nonempty (Fin m)) (oM.orientation x) hcardM
  let cd := basisOfOrientation (E := F) (fd := inferInstance)
    (⟨⟨0, hn⟩⟩ : Nonempty (Fin n)) (oN.orientation y) hcardN
  let b : Basis (Fin m) ℝ (TangentSpace I x) := bd.1
  let c : Basis (Fin n) ℝ (TangentSpace J y) := cd.1
  have hb : b.orientation = oM.orientation x := bd.2
  have hc : c.orientation = oN.orientation y := cd.2
  have hchar := productOrientation_characterization I J hm hn oM oN x y b c hb hc
  let A : TangentSpace I x ≃ₗ[ℝ] TangentSpace I' (f x) :=
    (f.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
  let B : TangentSpace J y ≃ₗ[ℝ] TangentSpace J' (g y) :=
    (g.mfderivToContinuousLinearEquiv (by simp) y).toLinearEquiv
  let D : TangentSpace (I.prod J) (x, y) ≃ₗ[ℝ] TangentSpace (I'.prod J') (f x, g y) :=
    ((f.prodCongr g).mfderivToContinuousLinearEquiv (by simp) (x, y)).toLinearEquiv
  let D' : TangentSpace (I.prod J) (x, y) ≃ₗ[ℝ] TangentSpace (I'.prod J') (f x, g y) :=
    (tangentProdEquiv I J (x, y)).trans
      ((A.prodCongr B).trans (tangentProdEquiv I' J' (f x, g y)).symm)
  have hDD : D = D' := by
    apply LinearEquiv.ext
    intro v
    have hDcoe : ⇑D = ⇑(mfderiv (I.prod J) (I'.prod J')
        (f.prodCongr g : (M × N) → (M' × N')) (x, y)) := by
      change ⇑((f.prodCongr g).mfderivToContinuousLinearEquiv (by simp) (x, y))
        = ⇑(mfderiv (I.prod J) (I'.prod J') (f.prodCongr g : (M × N) → (M' × N'))
            (x, y))
      exact congrArg DFunLike.coe
        (Diffeomorph.mfderivToContinuousLinearEquiv_coe (f.prodCongr g) (by simp))
    rw [hDcoe, Diffeomorph.coe_prodCongr,
      mfderiv_prodMap (f.mdifferentiable (by simp) x) (g.mdifferentiable (by simp) y)]
    change (mfderiv I I' (f : M → M') x v.1, mfderiv J J' (g : N → N') y v.2) = D' v
    dsimp only [D']
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply,
      tangentProdEquiv_apply_eq_self (I := I) (J := J) (x, y),
      LinearEquiv.prodCongr_apply,
      tangentProdEquiv_symm_apply_eq_self (I := I') (J := J') (f x, g y)]
    refine Prod.ext ?_ ?_
    · dsimp only [A]
      rw [ContinuousLinearEquiv.coe_toLinearEquiv,
        ← Diffeomorph.mfderivToContinuousLinearEquiv_coe f (by simp)]
      rfl
    · dsimp only [B]
      rw [ContinuousLinearEquiv.coe_toLinearEquiv,
        ← Diffeomorph.mfderivToContinuousLinearEquiv_coe g (by simp)]
      rfl
  have hb' : (b.map A).orientation = oM'.orientation (f x) := by
    rw [Basis.orientation_map, hb, hf x]
  have hc' : (c.map B).orientation = oN'.orientation (g y) := by
    rw [Basis.orientation_map, hc, hg y]
  have hchar' := productOrientation_characterization I' J' hm hn oM' oN' (f x) (g y)
    (b.map A) (c.map B) hb' hc'
  have hstep : Orientation.map (Fin (m + n)) D
      ((productOrientation I J hm hn oM oN).orientation (x, y))
      = (productOrientation I' J' hm hn oM' oN').orientation (f x, g y) := by
    rw [← hchar, hDD]
    calc Orientation.map (Fin (m + n)) D' ((productTangentBasis I J b c).orientation)
        = Orientation.map (Fin (m + n)) ((A.prodCongr B).trans
            (tangentProdEquiv I' J' (f x, g y)).symm)
            (Orientation.map (Fin (m + n)) (tangentProdEquiv I J (x, y))
              ((productTangentBasis I J b c).orientation)) :=
          orientation_map_trans_fin (tangentProdEquiv I J (x, y)) _ _
      _ = Orientation.map (Fin (m + n)) ((A.prodCongr B).trans
            (tangentProdEquiv I' J' (f x, g y)).symm)
            ((productTangentBasis I J b c).orientation) := by
          rw [orientation_map_tangentProdEquiv]
      _ = Orientation.map (Fin (m + n)) (tangentProdEquiv I' J' (f x, g y)).symm
            (Orientation.map (Fin (m + n)) (A.prodCongr B)
              ((productTangentBasis I J b c).orientation)) :=
          orientation_map_trans_fin (A.prodCongr B) _ _
      _ = Orientation.map (Fin (m + n)) (A.prodCongr B)
            ((productTangentBasis I J b c).orientation) := by
          rw [orientation_map_tangentProdEquiv_symm]
      _ = (productTangentBasis I' J' (b.map A) (c.map B)).orientation :=
          productTangentBasis_orientation_map b c A B
      _ = (productOrientation I' J' hm hn oM' oN').orientation (f x, g y) := hchar'
  change Orientation.map (Fin (m + n)) D
    ((productOrientation I J hm hn oM oN).orientation (x, y))
    = (productOrientation I' J' hm hn oM' oN').orientation (f x, g y)
  exact hstep

end DifferentialGeometry
