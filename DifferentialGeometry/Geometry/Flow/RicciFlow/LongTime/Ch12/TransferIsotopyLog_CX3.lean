import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TransferIsotopyFinal_S15

set_option autoImplicit false

/-!
# CH12-CX3: one smooth logarithm on a neighborhood of the diagonal

The minimizing-vector choice is made before the map `Φ`.  Near the diagonal it
agrees with every minimizing section supplied by `exists_transfer_section_S15`.
-/

noncomputable section
open scoped Manifold ContDiff Topology ENNReal
open Set Function Bundle Filter Metric

namespace GC.LongTime.Ch12
open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

variable (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)

/-- A total choice of minimizing logarithm; values outside finite-distance pairs
are zero and are never used in the smooth-diagonal statements. -/
def transferLog_CX3 (z : M × M) : TangentBundle I M :=
  ⟨z.1, if h : Manifold.riemannianEDist I z.1 z.2 ≠ ⊤ then
    Classical.choose (hopf_rinow_expMapIntrinsic_surjective_minimizing_of_ne_top g hEnorm z.1 z.2 h)
    else 0⟩

theorem transferLog_proj_CX3 (z : M × M) : (transferLog_CX3 g hEnorm z).proj = z.1 := rfl

theorem transferLog_spec_CX3 {z : M × M} (h : Manifold.riemannianEDist I z.1 z.2 ≠ ⊤) :
    expMapIntrinsic g hEnorm z.1 (transferLog_CX3 g hEnorm z).snd = z.2 ∧
      tanLen_S15 g (transferLog_CX3 g hEnorm z) =
        (Manifold.riemannianEDist I z.1 z.2).toReal := by
  simp only [transferLog_CX3, dite_eq_left h, tanLen_S15]
  exact Classical.choose_spec
    (hopf_rinow_expMapIntrinsic_surjective_minimizing_of_ne_top g hEnorm z.1 z.2 h)

theorem transferLog_zero_CX3 (p : M) :
    transferLog_CX3 g hEnorm (p, p) = (⟨p, (0 : TangentSpace I p)⟩ : TangentBundle I M) := by
  have hlen := (transferLog_spec_CX3 g hEnorm (z := (p, p)) (by simp [Manifold.riemannianEDist_self])).2
  have hv : (transferLog_CX3 g hEnorm (p, p)).snd = 0 := by
    by_contra hn
    have hp := tanLen_pos_S15 g p (transferLog_CX3 g hEnorm (p, p)).snd hn
    change 0 < tanLen_S15 g (transferLog_CX3 g hEnorm (p, p)) at hp
    simp only [hlen, Manifold.riemannianEDist_self, ENNReal.toReal_zero, lt_self_iff_false] at hp
  exact TotalSpace.ext rfl (heq_of_eq hv)

variable [LocallyCompactSpace M]

/-- On an open neighborhood of the entire diagonal, the logarithm is smooth and
is the unique minimizing inverse.  This uniqueness identifies the S15 witness. -/
theorem exists_transferLog_domain_CX3 :
    ∃ N : Set (M × M), IsOpen N ∧ (∀ p : M, (p, p) ∈ N) ∧
      ContMDiffOn (I.prod I) I.tangent ∞ (transferLog_CX3 g hEnorm) N ∧
      ∀ z ∈ N, ∀ w : TangentSpace I z.1,
        expMapIntrinsic g hEnorm z.1 w = z.2 →
        Real.sqrt (g.inner z.1 w w) = (Manifold.riemannianEDist I z.1 z.2).toReal →
        transferLog_CX3 g hEnorm z = (⟨z.1, w⟩ : TangentBundle I M) := by
  classical
  let B : ∀ p : M, DiagonalInverseBranch g hEnorm p :=
    fun p => standardDiagonalInverseBranch g hEnorm p
  have htube : ∀ p : M, ∃ W ∈ 𝓝 p, ∃ r : ℝ, 0 < r ∧
      ∀ u : TangentBundle I M, u.proj ∈ W → tanLen_S15 g u < r → u ∈ (B p).hom.source :=
    fun p => exists_short_vectors_subset_S15 g (B p).hom.open_source (B p).zero_mem
  choose W hW r hr htube using htube
  let V : M → Set (M × M) := fun p =>
    {z | z.1 ∈ interior (W p) ∧ Manifold.riemannianEDist I z.1 z.2 < ENNReal.ofReal (r p)}
  have hdist : Continuous (fun z : M × M => Manifold.riemannianEDist I z.1 z.2) := by
    let : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
    exact continuous_fst.edist continuous_snd
  have hV : ∀ p, IsOpen (V p) := fun p =>
    (isOpen_interior.preimage continuous_fst).inter (isOpen_lt hdist continuous_const)
  have hdiag : ∀ p, (p, p) ∈ V p := fun p =>
    ⟨mem_interior_iff_mem_nhds.mpr (hW p), by
      simpa only [Manifold.riemannianEDist_self, ENNReal.ofReal_pos] using hr p⟩
  have hagree : ∀ p, ∀ z ∈ V p,
      transferLog_CX3 g hEnorm z = (B p).inv z ∧ z ∈ (B p).dom := by
    intro p z hz
    have hfin : Manifold.riemannianEDist I z.1 z.2 ≠ ⊤ :=
      ne_of_lt (hz.2.trans ENNReal.ofReal_lt_top)
    obtain ⟨hexp, hlen⟩ := transferLog_spec_CX3 g hEnorm hfin
    have hs : transferLog_CX3 g hEnorm z ∈ (B p).hom.source :=
      htube p _ (interior_subset hz.1) (by
        rw [hlen]; exact (ENNReal.lt_ofReal_iff_toReal_lt hfin).mp hz.2)
    have heq := (B p).inv_eq_of_exp hs hexp
    have hmap := (B p).hom.map_source hs
    have hhom : (B p).hom (transferLog_CX3 g hEnorm z) =
        diagExp g hEnorm (transferLog_CX3 g hEnorm z) := (B p).hom_eq hs
    rw [hhom] at hmap
    have hd : diagExp g hEnorm (transferLog_CX3 g hEnorm z) = z := by
      exact Prod.ext rfl hexp
    rw [hd] at hmap
    exact ⟨heq.symm, hmap⟩
  refine ⟨⋃ p, V p, isOpen_iUnion hV, fun p => mem_iUnion.mpr ⟨p, hdiag p⟩, ?_, ?_⟩
  · apply contMDiffOn_of_locally_contMDiffOn
    intro z hz
    obtain ⟨p, hp⟩ := mem_iUnion.mp hz
    refine ⟨V p, hV p, hp, ?_⟩
    exact ((B p).inv_contMDiffOn.mono (fun y hy => (hagree p y hy.2).2)).congr
      (fun y hy => (hagree p y hy.2).1)
  · intro z hz w hexp hlen
    obtain ⟨p, hp⟩ := mem_iUnion.mp hz
    have hfin : Manifold.riemannianEDist I z.1 z.2 ≠ ⊤ :=
      ne_of_lt (hp.2.trans ENNReal.ofReal_lt_top)
    have hs : (⟨z.1, w⟩ : TangentBundle I M) ∈ (B p).hom.source :=
      htube p _ (interior_subset hp.1) (by
        change Real.sqrt (g.inner z.1 w w) < r p
        rw [hlen]; exact (ENNReal.lt_ofReal_iff_toReal_lt hfin).mp hp.2)
    exact (hagree p z hp).1.trans ((B p).inv_eq_of_exp hs hexp)

end GC.LongTime.Ch12
