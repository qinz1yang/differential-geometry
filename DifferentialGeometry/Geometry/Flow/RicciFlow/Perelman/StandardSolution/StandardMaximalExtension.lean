import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardSolution
import Mathlib.Order.Zorn

set_option autoImplicit false
noncomputable section
open Set Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
namespace PartialStandardSolution

theorem exists_chain_upper_bound (C : Set PartialStandardSolution)
    (hC : C.Nonempty) (hchain : IsChain IsExtendedBy C) :
    ∃ U : PartialStandardSolution, U.lifetime = sSup (lifetime '' C) ∧
      ∀ S ∈ C, S.IsExtendedBy U := by
  classical
  let T := sSup (lifetime '' C)
  have hle (S : PartialStandardSolution) (hS : S ∈ C) : S.lifetime ≤ T :=
    le_sSup ⟨S, hS, rfl⟩
  have hT : 0 < T := by
    obtain ⟨S, hS⟩ := hC
    exact S.lifetime_pos.trans_le (hle S hS)
  let D := lifetimeInterval T hT
  have hcover (t : ℝ) (ht : t ∈ D.carrier) : ∃ S ∈ C, t ∈ S.domain := by
    have hmem := (mem_lifetimeInterval_carrier T hT t).mp ht
    obtain ⟨L, ⟨S, hSC, rfl⟩, htS⟩ := lt_sSup_iff.mp hmem.2
    exact ⟨S, hSC, (mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos t).mpr ⟨hmem.1, htS⟩⟩
  choose cover hcover_mem hcover_time using hcover
  let g : ℝ → SmoothRiemannianMetric (𝓡 3) E3 := fun t =>
    if ht : t ∈ D.carrier then (cover t ht).metric t else DifferentialGeometry.PDE.RicciFlow.StandardCap.metric
  have hagree (S : PartialStandardSolution) (hSC : S ∈ C) (t : ℝ) (ht : t ∈ S.domain) :
      g t = S.metric t := by
    have htD : t ∈ D.carrier := lifetimeInterval_carrier_mono S.lifetime_pos hT (hle S hSC) ht
    simp only [g, dite_eq_left htD]
    by_cases heq : cover t htD = S
    · rw [heq]
    · rcases hchain (hcover_mem t htD) hSC heq with he | he
      · exact (he.2 t (hcover_time t htD)).symm
      · exact he.2 t ht
  have hsmooth : ContDiffOn ℝ ∞ (F := E3 →L[ℝ] E3 →L[ℝ] ℝ)
      (fun p : ℝ × E3 => by exact (g p.1).inner p.2) (D.carrier ×ˢ (univ : Set E3)) := by
    apply contDiffOn_of_locally_contDiffOn
    intro p hp
    let S := cover p.1 hp.1
    have hSC : S ∈ C := hcover_mem p.1 hp.1
    have hpS : p.1 ∈ S.domain := hcover_time p.1 hp.1
    let O : Set (ℝ × E3) := {q | ENNReal.ofReal q.1 < S.lifetime}
    have hO : IsOpen O := isOpen_lt (ENNReal.continuous_ofReal.comp continuous_fst) continuous_const
    refine ⟨O, hO, ((mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos p.1).mp hpS).2, ?_⟩
    have hsub : (D.carrier ×ˢ (univ : Set E3)) ∩ O ⊆ S.domain ×ˢ (univ : Set E3) := by
      intro q hq
      exact ⟨(mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos q.1).mpr
        ⟨((mem_lifetimeInterval_carrier T hT q.1).mp hq.1.1).1, hq.2⟩, mem_univ _⟩
    apply (S.smooth.mono hsub).congr
    intro q hq
    rw [hagree S hSC q.1 (hsub hq).1]
  have hequation : ∀ t ∈ D.carrier, ∀ (x : E3) (v w : TangentSpace (𝓡 3) x),
      HasDerivWithinAt (fun r => (g r).inner x v w)
        (-2 * ricciTensor (g t) x v w) (Ici 0) t := by
    intro t ht x v w
    let S := cover t ht
    have hSC : S ∈ C := hcover_mem t ht
    have htS : t ∈ S.domain := hcover_time t ht
    have hO : IsOpen {r : ℝ | ENNReal.ofReal r < S.lifetime} :=
      isOpen_lt ENNReal.continuous_ofReal continuous_const
    have hn := hO.mem_nhds ((mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos t).mp htS).2
    have he : (fun r => (g r).inner x v w) =ᶠ[𝓝[Ici 0] t]
        (fun r => (S.metric r).inner x v w) := by
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hn] with r hr hrS
      exact congrArg (fun m : SmoothRiemannianMetric (𝓡 3) E3 => m.inner x v w)
        (hagree S hSC r ((mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos r).mpr ⟨hr, hrS⟩))
    have het := hagree S hSC t htS
    have hh := (S.equation t htS x v w).congr_of_eventuallyEq he
      (congrArg (fun m : SmoothRiemannianMetric (𝓡 3) E3 => m.inner x v w) het)
    rw [← het] at hh
    exact hh
  have hzero : (0 : ℝ) ∈ D.carrier :=
    (mem_lifetimeInterval_carrier T hT 0).mpr ⟨le_rfl, by simpa only [ENNReal.ofReal_zero] using hT⟩
  have hinitial : g 0 = DifferentialGeometry.PDE.RicciFlow.StandardCap.metric :=
    (hagree (cover 0 hzero) (hcover_mem 0 hzero) 0 (hcover_time 0 hzero)).trans
      (cover 0 hzero).initial
  have hcomplete : ∀ t ∈ D.carrier, RiemannianMetricComplete (g t) := by
    intro t ht
    rw [hagree (cover t ht) (hcover_mem t ht) t (hcover_time t ht)]
    exact (cover t ht).complete t (hcover_time t ht)
  have hbound : ∀ θ : ℝ, 0 ≤ θ → ENNReal.ofReal θ < T →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc 0 θ, ∀ x : E3,
        Real.sqrt (normSq0S (g t) x 4 (metricRm04 (g t) x)) ≤ K := by
    intro θ hθ hθT
    have hθD : θ ∈ D.carrier := (mem_lifetimeInterval_carrier T hT θ).mpr ⟨hθ, hθT⟩
    let S := cover θ hθD
    have hSC : S ∈ C := hcover_mem θ hθD
    have hθS := ((mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos θ).mp
      (hcover_time θ hθD)).2
    obtain ⟨K, hK, hb⟩ := S.curvature_bound θ hθ hθS
    refine ⟨K, hK, ?_⟩
    intro t ht x
    have htS : t ∈ S.domain := (Icc_subset_lifetimeInterval_iff S.lifetime S.lifetime_pos θ hθ).mpr hθS ht
    rw [hagree S hSC t htS]
    exact hb t ht x
  let U : PartialStandardSolution :=
    ⟨T, hT, g, hsmooth, hequation, hinitial, hcomplete, hbound⟩
  exact ⟨U, rfl, fun S hS => ⟨hle S hS, hagree S hS⟩⟩

theorem exists_maximal_extension (S : PartialStandardSolution) :
    ∃ U : StandardSolution, S.IsExtendedBy U.val := by
  let : Preorder PartialStandardSolution :=
    { le := IsExtendedBy
      le_refl := isExtendedBy_refl
      le_trans := fun _ _ _ => isExtendedBy_trans }
  have hb (C : Set PartialStandardSolution) (hchain : IsChain (· ≤ ·) C) (hC : C.Nonempty) :
      ∃ U : PartialStandardSolution, ∀ Q ∈ C, Q ≤ U := by
    obtain ⟨U, _, hU⟩ := exists_chain_upper_bound C hC hchain
    exact ⟨U, hU⟩
  obtain ⟨U, hSU, hmax⟩ := zorn_le_nonempty_Ici₀ S
    (fun C _ hc Q hQ => hb C hc ⟨Q, hQ⟩) S le_rfl
  exact ⟨⟨U, hmax⟩, hSU⟩
end PartialStandardSolution
end DifferentialGeometry.PDE.RicciFlow
