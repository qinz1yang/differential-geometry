import DifferentialGeometry.Topology.VectorField.BoundaryOutwardization
import DifferentialGeometry.Topology.VectorField.InwardCollarIndexSum
import DifferentialGeometry.Topology.VectorField.OutwardPoincareHopf

set_option autoImplicit false
noncomputable section
open Set Bundle Filter Manifold TopologicalSpace
open scoped ContDiff Topology
namespace DifferentialGeometry.VectorField

theorem relativePoincareHopf_of_collar
    {d : ℕ} {H B : Type*} {M : Type}
    [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B] [CompactSpace B]
    (J : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (d + 1))) H) [IsManifold J 1 B]
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (d + 2)) M]
    [IsManifold (𝓡∂ (d + 2)) ∞ M] [T2Space M] [CompactSpace M]
    {ε δ : ℝ} [Fact ((0 : ℝ) < ε)] (hδ : 0 < δ) (hδε : δ < ε) :
    let I := 𝓡∂ (d + 2)
    let S : Opens (B × Icc (0 : ℝ) ε) :=
      ⟨{q | q.2.val < δ}, isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const⟩
    ∀ (Y : Opens M), I.boundary M ⊆ Y →
    ∀ e : Diffeomorph (J.prod (𝓡∂ 1)) I S Y ∞,
      (∀ q : S, 0 < q.val.2.val → I.IsInteriorPoint (e q).val) →
    ∀ V : ∀ x : M, TangentSpace I x,
      ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)) →
    ∀ (hVf : {x | V x = 0}.Finite)
      (hVi : ∀ x, V x = 0 → HasContinuousIsolatedZero I V x)
      (hVI : ∀ x, V x = 0 → I.IsInteriorPoint x),
    let W := _root_.VectorField.mpullback (J.prod (𝓡∂ 1)) I e (fun y : Y => V y.val)
    (∀ q : S, W q ≠ 0) →
    let z : B → S := fun p => ⟨(p, ⟨0, ⟨le_rfl, (Fact.out : (0 : ℝ) < ε).le⟩⟩), hδ⟩
    let T : ∀ p : B, TangentSpace J p := fun p => (W (z p)).1
    let b : B → ℝ := fun p =>
      -(DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc (z p).val.2 (W (z p)).2)
    ∀ (hTf : {p | T p = 0}.Finite)
      (hTi : ∀ p, T p = 0 → HasContinuousIsolatedZero J T p)
      (hTI : ∀ p, T p = 0 → J.IsInteriorPoint p)
      (K : Type) [Field K],
      interiorIndexSum I V hVf hVi hVI + interiorIndexSumOn J T hTf hTi hTI {p | b p < 0} =
        DifferentialGeometry.Homology.eulerChar K (TopCat.of M) := by
  intro I S Y hY e hi V hV hVf hVi hVI W hn z T b hTf hTi hTI K _
  let a := δ / 8
  have ha : 0 < a := div_pos hδ (by norm_num)
  have haδ : 4 * a < δ := by dsimp [a]; linarith
  have haε : a ≤ ε := by linarith
  have hW : ContMDiff (J.prod (𝓡∂ 1)) (J.prod (𝓡∂ 1)).tangent ∞
      (fun q => (⟨q, W q⟩ : TangentBundle (J.prod (𝓡∂ 1)) S)) := by
    have hVr := contMDiff_tangentSection_restrict_opens Y hV.contMDiffOn
    intro q
    exact contMDiffAt_mpullback_partialDiffeomorph e.toPartialDiffeomorph (by simp)
      (by trivial) (hVr (e q))
  have hz : ContMDiff J (J.prod (𝓡∂ 1)) ∞ z := by
    apply (ContMDiff.subtypeVal_comp_iff S z).mp
    exact contMDiff_id.prodMk contMDiff_const
  have hcomponents := contMDiff_equivTangentBundleProd.comp
    (((contMDiff_tangentSection_opens_iff S W).mp hW).comp hz)
  have hb : ContMDiff J 𝓘(ℝ, ℝ) ∞ (fun p => b p / a) := by
    have hs := DifferentialGeometry.Manifold.Interval.contMDiff_tangentCoordinateIcc.comp hcomponents.snd
    have hl : ContDiff ℝ ∞ (fun t : ℝ => -t / a) := by fun_prop
    exact hl.contMDiff.comp hs
  obtain ⟨L, _, hLinner, G, hGeq, hG, hout, hgerm, hzero, hdis, hbij, hheight, hfinite⟩ :=
    exists_outward_replacement_in_collar hδ hδε ha haδ Y hY e hi V hV hn
  have hGf := hfinite hTf hVf
  have hGi (x : M) (hx : G x = 0) : HasContinuousIsolatedZero I G x := by
    refine ⟨hx, ⟨univ, univ_mem, hG.continuous.continuousOn⟩, ?_⟩
    have hclosed := (show ({y | G y = 0} \ {x}).Finite from hGf.sdiff).isClosed
    filter_upwards [hclosed.isOpen_compl.mem_nhds
      (show x ∈ ({y | G y = 0} \ {x})ᶜ by simp)] with y hy
    intro hyG
    by_contra hne
    exact hy ⟨hyG, hne⟩
  have hGI (x : M) (hx : G x = 0) : I.IsInteriorPoint x := by
    by_contra h
    have hh := hout x ((I.isBoundaryPoint_iff_not_isInteriorPoint x).mpr h)
    rw [hx] at hh
    exact (lt_irrefl 0) hh
  have hχ := interiorIndexSum_eq_eulerChar_of_outward G hG hout hGf hGi hGI K
  subst G
  have hsum := interiorIndexSum_inwardCollar_patch J I ha haε S Y e V T (fun p => b p / a) L
    hLinner hheight hbij (hb.of_le (by simp)) hTf hTi hTI hVf hVi hVI hGf hGi hGI hzero hdis hgerm
  have hregion : {p | b p / a < 0} = {p | b p < 0} := by
    ext p
    change b p / a < 0 ↔ b p < 0
    simpa only [zero_mul] using (div_lt_iff₀ ha : b p / a < 0 ↔ b p < 0 * a)
  rw [hregion] at hsum
  exact hsum.symm.trans hχ

end DifferentialGeometry.VectorField
