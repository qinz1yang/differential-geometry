import DifferentialGeometry.Topology.VectorField.CollarExtension
import DifferentialGeometry.Topology.VectorField.ContinuousIsolatedZero

set_option autoImplicit false
open Bundle Filter Set
open scoped Manifold ContDiff Topology
noncomputable section
namespace Poincare.VectorField
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ E H) [IsManifold I 1 M]

theorem HasContinuousIsolatedZero.collarExtension
    {T : ∀ x : M, TangentSpace I x} {b : M → ℝ} {x : M} {t : ℝ}
    (hT : HasContinuousIsolatedZero I T x) (hb : ∃ s ∈ 𝓝 x, ContinuousOn b s)
    (hb0 : b x ≠ 0) (hz : Poincare.VectorField.collarExtension T b collarTransition (x, t) = 0) :
    HasContinuousIsolatedZero (I.prod 𝓘(ℝ, ℝ)) (Poincare.VectorField.collarExtension T b collarTransition) (x, t) where
  zero := hz
  continuous := by
    obtain ⟨s, hs, hTs⟩ := hT.continuous
    obtain ⟨U, hUs, hU, hxU⟩ := mem_nhds_iff.mp hs
    obtain ⟨B, hB, hbB⟩ := hb
    obtain ⟨V, hVB, hV, hxV⟩ := mem_nhds_iff.mp hB
    refine ⟨(U ∩ V) ×ˢ univ, (hU.inter hV).prod isOpen_univ |>.mem_nhds ⟨⟨hxU, hxV⟩, trivial⟩, ?_⟩
    intro p hp
    have hTp : ContMDiffAt I I.tangent 0 (fun y => (⟨y, T y⟩ : TangentBundle I M)) p.1 :=
      (contMDiffOn_zero_iff.mpr (hTs.mono hUs)).contMDiffAt (hU.mem_nhds hp.1.1)
    have hbp : ContMDiffAt I 𝓘(ℝ, ℝ) 0 b p.1 :=
      (contMDiffOn_zero_iff.mpr (hbB.mono hVB)).contMDiffAt (hV.mem_nhds hp.1.2)
    have hr : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 0
        (fun q : M × ℝ => collarTransition q.2) p :=
      ((contDiff_collarTransition.of_le (by simp)).contMDiff.contMDiffAt).comp p contMDiffAt_snd
    have hN : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 0
        (fun q : M × ℝ => (1 - collarTransition q.2) * b q.1 + collarTransition q.2) p :=
      ((contMDiffAt_const.sub hr).mul (hbp.comp p contMDiffAt_fst)).add hr
    have hR : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ).tangent 0
        (fun q : M × ℝ => (⟨q.2, (1 - collarTransition q.2) * b q.1 + collarTransition q.2⟩ :
          TangentBundle 𝓘(ℝ, ℝ) ℝ)) p := by
      apply Bundle.contMDiffAt_totalSpace.mpr
      refine ⟨contMDiffAt_snd, ?_⟩
      convert hN using 1
      simp
    exact ((contMDiff_equivTangentBundleProd_symm (I := I) (I' := 𝓘(ℝ, ℝ)) (n := 0)).contMDiffAt.comp p
      ((hTp.comp p contMDiffAt_fst).prodMk hR)).continuousAt.continuousWithinAt
  isolated := by
    obtain ⟨_, hbin, _⟩ := (collarExtension_eq_zero_iff (fun _ => hb0)
      (collarTransition_mem_Icc t)).mp hz
    obtain ⟨u, _, huniq⟩ := existsUnique_collarExtension_eq_zero hT.zero hbin
    have htu : t = u := huniq t hz
    filter_upwards [continuous_fst.continuousAt.eventually hT.isolated] with p hp
    intro hpz
    rcases p with ⟨y, s⟩
    have hy : y = x := hp (congrArg Prod.fst hpz)
    subst y
    exact Prod.ext rfl ((huniq s hpz).trans htu.symm)


theorem HasContinuousIsolatedZero.collarExtension_of_contMDiffAt
    {T : ∀ x : M, TangentSpace I x} {b : M → ℝ} {x : M} {t : ℝ}
    (hT : HasContinuousIsolatedZero I T x) (hb : ContMDiffAt I 𝓘(ℝ, ℝ) 1 b x)
    (hb0 : b x ≠ 0) (hz : Poincare.VectorField.collarExtension T b collarTransition (x, t) = 0) :
    HasContinuousIsolatedZero (I.prod 𝓘(ℝ, ℝ)) (Poincare.VectorField.collarExtension T b collarTransition) (x, t) := by
  obtain ⟨s, hs, hc⟩ := (contMDiffAt_iff_contMDiffOn_nhds (by simp : (1 : ℕ∞ω) ≠ ∞)).mp hb
  exact hT.collarExtension I ⟨s, hs, hc.continuousOn⟩ hb0 hz

end Poincare.VectorField
