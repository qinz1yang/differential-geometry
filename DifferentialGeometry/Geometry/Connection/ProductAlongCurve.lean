import DifferentialGeometry.Geometry.Connection.Product
import DifferentialGeometry.Geometry.Connection.LeviCivita.AlongCurve

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Connection

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {K : Type*} [TopologicalSpace K] {I' : ModelWithCorners ℝ F K}
    {N : Type*} [TopologicalSpace N] [ChartedSpace K N] [IsManifold I' ∞ N]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ F] [IsManifold I' ∞ N] in
private theorem tangentBundleProd_symm_apply (q : TangentBundle I M × TangentBundle I' N) :
    (equivTangentBundleProd I M I' N).symm q =
      (⟨(q.1.proj, q.2.proj), (q.1.snd, q.2.snd)⟩ :
        TangentBundle (I.prod I') (M × N)) := rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private theorem mdifferentiableWithinAt_tangentBundle_prod {γ : ℝ → M} {γ' : ℝ → N}
    {Z : ∀ t, TangentSpace I (γ t)} {Z' : ∀ t, TangentSpace I' (γ' t)} {s : Set ℝ} {x : ℝ}
    (hZ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I.tangent
      (fun u => (⟨γ u, Z u⟩ : TangentBundle I M)) s x)
    (hZ' : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I'.tangent
      (fun u => (⟨γ' u, Z' u⟩ : TangentBundle I' N)) s x) :
    MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod I').tangent
      (fun u => (⟨(γ u, γ' u), (Z u, Z' u)⟩ : TangentBundle (I.prod I') (M × N))) s x := by
  have hpair : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.tangent.prod I'.tangent)
      (fun u => ((⟨γ u, Z u⟩ : TangentBundle I M),
        (⟨γ' u, Z' u⟩ : TangentBundle I' N))) s x :=
    hZ.prodMk hZ'
  have hsm : MDifferentiable (I.tangent.prod I'.tangent) (I.prod I').tangent
      ⇑(equivTangentBundleProd I M I' N).symm :=
    (contMDiff_equivTangentBundleProd_symm (I := I) (I' := I') (M := M) (M' := N)
      (n := ∞)).mdifferentiable (by simp)
  have hcomp := ((hsm _).mdifferentiableWithinAt (s := Set.univ)).comp x hpair
    (Set.subset_univ s)
  exact hcomp.congr (fun u _ => rfl) rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private theorem trivializationAt_continuousLinearMapAt_prod_point
    (p : M × N) {q : M × N}
    (hq : q ∈ (trivializationAt (E × F) (TangentSpace (I.prod I')) p).baseSet)
    (v : TangentSpace (I.prod I') q) :
    (trivializationAt (E × F) (TangentSpace (I.prod I')) p).continuousLinearMapAt ℝ q v =
      ((trivializationAt E (TangentSpace I) p.1).continuousLinearMapAt ℝ q.1 v.1,
       (trivializationAt F (TangentSpace I') p.2).continuousLinearMapAt ℝ q.2 v.2) := by
  have hq' : q.1 ∈ (trivializationAt E (TangentSpace I) p.1).baseSet ∧
      q.2 ∈ (trivializationAt F (TangentSpace I') p.2).baseSet := by
    have h := hq
    rw [TangentBundle.trivializationAt_baseSet, prodChartedSpace_chartAt,
      OpenPartialHomeomorph.prod_source] at h
    exact h
  have hsym : (trivializationAt (E × F) (TangentSpace (I.prod I')) p).symmL ℝ q
      ((trivializationAt E (TangentSpace I) p.1).continuousLinearMapAt ℝ q.1 v.1,
       (trivializationAt F (TangentSpace I') p.2).continuousLinearMapAt ℝ q.2 v.2) = v := by
    rw [trivializationAt_symmL_prod (I := I) (J := I') p q hq]
    exact Prod.ext (Trivialization.symmL_continuousLinearMapAt _ hq'.1 v.1)
      (Trivialization.symmL_continuousLinearMapAt _ hq'.2 v.2)
  have hkey := Trivialization.continuousLinearMapAt_symmL
    (R := ℝ) (e := trivializationAt (E × F) (TangentSpace (I.prod I')) p) hq
    ((trivializationAt E (TangentSpace I) p.1).continuousLinearMapAt ℝ q.1 v.1,
     (trivializationAt F (TangentSpace I') p.2).continuousLinearMapAt ℝ q.2 v.2)
  rw [hsym] at hkey
  exact hkey

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ F] [IsManifold I' ∞ N] in
private theorem derivWithin_pair {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {Y' : Type*} [NormedAddCommGroup Y'] [NormedSpace ℝ Y']
    (f : ℝ → Y) (g : ℝ → Y') {s : Set ℝ} {x : ℝ}
    (hf : DifferentiableWithinAt ℝ f s x) (hg : DifferentiableWithinAt ℝ g s x) :
    derivWithin (fun u => (f u, g u)) s x = (derivWithin f s x, derivWithin g s x) := by
  simp only [derivWithin]
  by_cases hU : UniqueDiffWithinAt ℝ s x
  · rw [hf.fderivWithin_prodMk hg hU, ContinuousLinearMap.prod_apply]
  · rw [fderivWithin_zero_of_not_uniqueDiffWithinAt hU,
      fderivWithin_zero_of_not_uniqueDiffWithinAt hU,
      fderivWithin_zero_of_not_uniqueDiffWithinAt hU]
    rfl

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem mfderivWithin_zero_of_not_uniqueDiffWithinAt
    {γ : ℝ → M} {s : Set ℝ} {x : ℝ} (h : ¬ UniqueDiffWithinAt ℝ s x) :
    mfderivWithin 𝓘(ℝ, ℝ) I γ s x = 0 := by
  by_cases hd : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s x
  · exact hd.mfderivWithin.trans
      (fderivWithin_zero_of_not_uniqueDiffWithinAt
        (f := writtenInExtChartAt 𝓘(ℝ, ℝ) I x γ)
        (fun h' : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) s x => h h'.uniqueDiffWithinAt))
  · exact mfderivWithin_zero_of_not_mdifferentiableWithinAt hd

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ F] [IsManifold I' ∞ N] in
private theorem mfderivWithin_prodMk_apply {γ : ℝ → M} {γ' : ℝ → N}
    {s : Set ℝ} {x : ℝ}
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s x)
    (hγ' : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I' γ' s x) :
    mfderivWithin 𝓘(ℝ, ℝ) (I.prod I') (fun u => (γ u, γ' u)) s x =
      (mfderivWithin 𝓘(ℝ, ℝ) I γ s x).prod (mfderivWithin 𝓘(ℝ, ℝ) I' γ' s x) := by
  by_cases hU : UniqueDiffWithinAt ℝ s x
  · exact mfderivWithin_prodMk hγ hγ' hU.uniqueMDiffWithinAt
  · rw [mfderivWithin_zero_of_not_uniqueDiffWithinAt (I := I.prod I') hU,
      mfderivWithin_zero_of_not_uniqueDiffWithinAt (I := I) hU,
      mfderivWithin_zero_of_not_uniqueDiffWithinAt (I := I') hU]
    rfl

theorem derivAlongWithin_prod [T2Space M] [T2Space N]
    (g : SmoothRiemannianMetric I M) (g' : SmoothRiemannianMetric I' N)
    (γ : ℝ → M) (γ' : ℝ → N)
    (Z : ∀ t, TangentSpace I (γ t)) (Z' : ∀ t, TangentSpace I' (γ' t))
    {s : Set ℝ} {x : ℝ}
    (hZ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I.tangent
      (fun u => (⟨γ u, Z u⟩ : TangentBundle I M)) s x)
    (hZ' : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I'.tangent
      (fun u => (⟨γ' u, Z' u⟩ : TangentBundle I' N)) s x) :
    (LeviCivita (g.prod g')).derivAlongWithin (fun u => (γ u, γ' u))
        (fun u => (Z u, Z' u)) s x =
      ((LeviCivita g).derivAlongWithin γ Z s x, (LeviCivita g').derivAlongWithin γ' Z' s x) := by
  have hpair := mdifferentiableWithinAt_tangentBundle_prod hZ hZ'
  have hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s x := by
    have h := (mdifferentiableWithinAt_totalSpace (IB := I) (IM := 𝓘(ℝ, ℝ))
      (f := fun u => (⟨γ u, Z u⟩ : TangentBundle I M)) (x₀ := x)).mp hZ
    simpa only using h.1
  have hγ' : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I' γ' s x := by
    have h := (mdifferentiableWithinAt_totalSpace (IB := I') (IM := 𝓘(ℝ, ℝ))
      (f := fun u => (⟨γ' u, Z' u⟩ : TangentBundle I' N)) (x₀ := x)).mp hZ'
    simpa only using h.1
  have hp : (γ x, γ' x) ∈ (trivializationAt (E × F) (TangentSpace (I.prod I'))
      (γ x, γ' x)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt (E × F) (TangentSpace (I.prod I')) (γ x, γ' x)
  have hp₁ : γ x ∈ (trivializationAt E (TangentSpace I) (γ x)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ x)
  have hp₂ : γ' x ∈ (trivializationAt F (TangentSpace I') (γ' x)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt F (TangentSpace I') (γ' x)
  have hw : (trivializationAt (E × F) (TangentSpace (I.prod I')) (γ x, γ' x)).continuousLinearMapAt
        ℝ (γ x, γ' x) (Z x, Z' x) =
      ((trivializationAt E (TangentSpace I) (γ x)).continuousLinearMapAt ℝ (γ x) (Z x),
       (trivializationAt F (TangentSpace I') (γ' x)).continuousLinearMapAt ℝ (γ' x) (Z' x)) :=
    trivializationAt_continuousLinearMapAt_prod (I := I) (J := I') (γ x, γ' x) (Z x, Z' x)
  have hX : mfderivWithin 𝓘(ℝ, ℝ) (I.prod I') (fun u => (γ u, γ' u)) s x =
      (mfderivWithin 𝓘(ℝ, ℝ) I γ s x).prod (mfderivWithin 𝓘(ℝ, ℝ) I' γ' s x) :=
    mfderivWithin_prodMk_apply hγ hγ'
  have hX₁ : (mfderivWithin 𝓘(ℝ, ℝ) (I.prod I') (fun u => (γ u, γ' u)) s x
      ((NormedSpace.fromTangentSpace x).symm 1)).1 =
      mfderivWithin 𝓘(ℝ, ℝ) I γ s x ((NormedSpace.fromTangentSpace x).symm 1) := by
    rw [hX]
    rfl
  have hX₂ : (mfderivWithin 𝓘(ℝ, ℝ) (I.prod I') (fun u => (γ u, γ' u)) s x
      ((NormedSpace.fromTangentSpace x).symm 1)).2 =
      mfderivWithin 𝓘(ℝ, ℝ) I' γ' s x ((NormedSpace.fromTangentSpace x).symm 1) := by
    rw [hX]
    rfl
  have hφ : (fun u => (trivializationAt (E × F) (TangentSpace (I.prod I'))
        (γ x, γ' x)).continuousLinearMapAt ℝ (γ u, γ' u) (Z u, Z' u)) =ᶠ[𝓝[s] x]
      (fun u => ((trivializationAt E (TangentSpace I) (γ x)).continuousLinearMapAt ℝ (γ u) (Z u),
        (trivializationAt F (TangentSpace I') (γ' x)).continuousLinearMapAt ℝ (γ' u) (Z' u))) := by
    have hcont : ContinuousWithinAt (fun u : ℝ => (γ u, γ' u)) s x :=
      hγ.continuousWithinAt.prodMk hγ'.continuousWithinAt
    filter_upwards [hcont.preimage_mem_nhdsWithin
      ((trivializationAt (E × F) (TangentSpace (I.prod I')) (γ x,
        γ' x)).open_baseSet.mem_nhds hp)] with u hu
    exact trivializationAt_continuousLinearMapAt_prod_point (I := I) (I' := I')
      (γ x, γ' x) hu (Z u, Z' u)
  have hA : derivWithin (fun u => (trivializationAt (E × F) (TangentSpace (I.prod I'))
        (γ x, γ' x)).continuousLinearMapAt ℝ (γ u, γ' u) (Z u, Z' u)) s x =
      (derivWithin (fun u =>
          (trivializationAt E (TangentSpace I) (γ x)).continuousLinearMapAt ℝ (γ u) (Z u)) s x,
       derivWithin (fun u =>
          (trivializationAt F (TangentSpace I') (γ' x)).continuousLinearMapAt ℝ (γ' u) (Z' u))
          s x) := by
    rw [hφ.derivWithin_eq hw]
    exact derivWithin_pair _ _
      (CovariantDerivative.hasDerivWithinAt_coord (LeviCivita g)
        (trivializationAt E (TangentSpace I) (γ x)) hp₁ hZ).differentiableWithinAt
      (CovariantDerivative.hasDerivWithinAt_coord (LeviCivita g')
        (trivializationAt F (TangentSpace I') (γ' x)) hp₂ hZ').differentiableWithinAt
  have hB : (LeviCivita (g.prod g')).connectionForm
        (trivializationAt (E × F) (TangentSpace (I.prod I')) (γ x, γ' x)) (γ x, γ' x)
        (mfderivWithin 𝓘(ℝ, ℝ) (I.prod I') (fun u => (γ u, γ' u)) s x
          ((NormedSpace.fromTangentSpace x).symm 1))
        ((trivializationAt (E × F) (TangentSpace (I.prod I')) (γ x, γ' x)).continuousLinearMapAt
          ℝ (γ x, γ' x) (Z x, Z' x)) =
      ((LeviCivita g).connectionForm (trivializationAt E (TangentSpace I) (γ x)) (γ x)
          (mfderivWithin 𝓘(ℝ, ℝ) I γ s x ((NormedSpace.fromTangentSpace x).symm 1))
          ((trivializationAt E (TangentSpace I) (γ x)).continuousLinearMapAt ℝ (γ x) (Z x)),
       (LeviCivita g').connectionForm (trivializationAt F (TangentSpace I') (γ' x)) (γ' x)
          (mfderivWithin 𝓘(ℝ, ℝ) I' γ' s x ((NormedSpace.fromTangentSpace x).symm 1))
          ((trivializationAt F (TangentSpace I') (γ' x)).continuousLinearMapAt ℝ (γ' x) (Z' x))) :=
    (connectionForm_leviCivita_prod (I := I) (J := I') g g' (γ x, γ' x) _ _).trans
      (by rw [hX₁, hX₂, congrArg Prod.fst hw, congrArg Prod.snd hw])
  rw [CovariantDerivative.derivAlongWithin_eq (LeviCivita (g.prod g'))
      (trivializationAt (E × F) (TangentSpace (I.prod I')) (γ x, γ' x)) hp hpair,
    CovariantDerivative.derivAlongWithin_eq (LeviCivita g)
      (trivializationAt E (TangentSpace I) (γ x)) hp₁ hZ,
    CovariantDerivative.derivAlongWithin_eq (LeviCivita g')
      (trivializationAt F (TangentSpace I') (γ' x)) hp₂ hZ',
    hA, hB, trivializationAt_symmL_prod (I := I) (J := I') (γ x, γ' x) (γ x, γ' x) hp,
    Prod.fst_add, Prod.snd_add]

theorem covDerivAlong_prod [T2Space M] [T2Space N]
    [BoundarylessManifold I M] [BoundarylessManifold I' N]
    (g : SmoothRiemannianMetric I M) (g' : SmoothRiemannianMetric I' N)
    (γ : ℝ → M) (γ' : ℝ → N)
    (Z : ∀ t, TangentSpace I (γ t)) (Z' : ∀ t, TangentSpace I' (γ' t)) (x : ℝ)
    (hZ : MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent
      (fun u => (⟨γ u, Z u⟩ : TangentBundle I M)) x)
    (hZ' : MDifferentiableAt 𝓘(ℝ, ℝ) I'.tangent
      (fun u => (⟨γ' u, Z' u⟩ : TangentBundle I' N)) x) :
    covDerivAlong (g.prod g') (fun u => (γ u, γ' u)) (fun u => (Z u, Z' u)) x =
      (covDerivAlong g γ Z x, covDerivAlong g' γ' Z' x) := by
  have hpair : MDifferentiableAt 𝓘(ℝ, ℝ) (I.prod I').tangent
      (fun u => (⟨(γ u, γ' u), (Z u, Z' u)⟩ : TangentBundle (I.prod I') (M × N))) x :=
    (mdifferentiableWithinAt_tangentBundle_prod (s := Set.univ)
      hZ.mdifferentiableWithinAt hZ'.mdifferentiableWithinAt).mdifferentiableAt (by simp)
  have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ x :=
    ((mdifferentiableAt_totalSpace I _).mp hZ).1
  have hγ' : MDifferentiableAt 𝓘(ℝ, ℝ) I' γ' x :=
    ((mdifferentiableAt_totalSpace I' _).mp hZ').1
  have h₁ := derivAlongWithin_leviCivita_eq_covDerivAlong g γ Z Filter.univ_mem hγ
    (BoundarylessManifold.isInteriorPoint (I := I) (x := γ x))
  have h₂ := derivAlongWithin_leviCivita_eq_covDerivAlong g' γ' Z' Filter.univ_mem hγ'
    (BoundarylessManifold.isInteriorPoint (I := I') (x := γ' x))
  have hpairBase : MDifferentiableAt 𝓘(ℝ, ℝ) (I.prod I') (fun u => (γ u, γ' u)) x :=
    ((mdifferentiableAt_totalSpace (I.prod I') _).mp hpair).1
  have h₃ := derivAlongWithin_leviCivita_eq_covDerivAlong (g.prod g')
    (fun u => (γ u, γ' u)) (fun u => (Z u, Z' u)) Filter.univ_mem hpairBase
    (BoundarylessManifold.isInteriorPoint (I := I.prod I') (x := (γ x, γ' x)))
  have hsplit := derivAlongWithin_prod (s := Set.univ) g g' γ γ' Z Z'
    (hZ.mdifferentiableWithinAt (s := Set.univ))
    (hZ'.mdifferentiableWithinAt (s := Set.univ))
  rw [← h₃, hsplit, h₁, h₂]

end DifferentialGeometry.Geometry.Connection
