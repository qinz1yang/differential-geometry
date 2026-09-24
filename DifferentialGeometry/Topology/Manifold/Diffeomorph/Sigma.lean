import DifferentialGeometry.Topology.Manifold.Sigma
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict
import DifferentialGeometry.Topology.Homeomorph.Sigma

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

variable {E H M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [Nonempty H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

theorem isLocalDiffeomorph_sum_inl : IsLocalDiffeomorph I I ∞ (Sum.inl : M → M ⊕ N) := by
  intro x
  let c := chartAt H x
  let d := c.lift_openEmbedding (_root_.Topology.IsOpenEmbedding.inl (X := M) (Y := N))
  let e := c.trans d.symm
  have hc : ContMDiffOn I I ∞ c c.source := contMDiffOn_chart
  have hc' : ContMDiffOn I I ∞ c.symm c.target := contMDiffOn_chart_symm
  have heqd : d = chartAt H (Sum.inl x : M ⊕ N) :=
    (ChartedSpace.sum_chartAt_inl x).symm
  have hd : ContMDiffOn I I ∞ d d.source := by
    rw [heqd]
    exact contMDiffOn_chart
  have hd' : ContMDiffOn I I ∞ d.symm d.target := by
    rw [heqd]
    exact contMDiffOn_chart_symm
  let D : PartialDiffeomorph I I M (M ⊕ N) ∞ :=
    { e with contMDiffOn_toFun := hd'.comp' hc, contMDiffOn_invFun := hc'.comp' hd }
  refine ⟨D, ⟨mem_chart_source H x, c.map_source (mem_chart_source H x)⟩, ?_⟩
  intro y hy
  change Sum.inl y = Sum.inl (c.symm (c y))
  rw [c.left_inv hy.1]

theorem isLocalDiffeomorph_sum_inr : IsLocalDiffeomorph I I ∞ (Sum.inr : M → N ⊕ M) := by
  have h := DifferentialGeometry.isLocalDiffeomorph_comp
    (Diffeomorph.sumComm I M ∞ N).isLocalDiffeomorph
    (isLocalDiffeomorph_sum_inl (I := I) (M := M) (N := N))
  exact h

universe u v w
variable {ι : Type v} {X : ι → Type u}
  [∀ i, TopologicalSpace (X i)] [∀ i, ChartedSpace H (X i)] [∀ i, IsManifold I ∞ (X i)]
  {F K P : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
  {J : ModelWithCorners ℝ F K} [TopologicalSpace P] [ChartedSpace K P]

theorem isLocalDiffeomorph_sigma_iff (f : (Σ i, X i) → P) :
    IsLocalDiffeomorph I J ∞ f ↔ ∀ i, IsLocalDiffeomorph I J ∞ (f ∘ Sigma.mk i) := by
  constructor
  · intro hf i
    exact DifferentialGeometry.isLocalDiffeomorph_comp hf (isLocalDiffeomorph_sigmaMk i)
  · rintro hf ⟨i, x⟩
    exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp (hf i x) (isLocalDiffeomorph_sigmaMk i x)

variable {Y : ι → Type w} [∀ i, TopologicalSpace (Y i)] [∀ i, ChartedSpace H (Y i)]
  [∀ i, IsManifold I ∞ (Y i)]

def sigmaCongrRightDiffeomorph (D : ∀ i, Diffeomorph I I (X i) (Y i) ∞) :
    Diffeomorph I I (Σ i, X i) (Σ i, Y i) ∞ := by
  let f : (Σ i, X i) → Σ i, Y i := fun x => ⟨x.fst, D x.fst x.snd⟩
  have hf : IsLocalDiffeomorph I I ∞ f := by
    apply (isLocalDiffeomorph_sigma_iff f).mpr
    intro i
    change IsLocalDiffeomorph I I ∞ (Sigma.mk i ∘ D i)
    exact DifferentialGeometry.isLocalDiffeomorph_comp (isLocalDiffeomorph_sigmaMk (M := Y) i) (D i).isLocalDiffeomorph
  exact hf.diffeomorphOfBijective (Equiv.sigmaCongrRight fun i => (D i).toEquiv).bijective

@[simp] theorem sigmaCongrRightDiffeomorph_apply
    (D : ∀ i, Diffeomorph I I (X i) (Y i) ∞) (i : ι) (x : X i) :
    sigmaCongrRightDiffeomorph D ⟨i, x⟩ = ⟨i, D i x⟩ := rfl

variable {V : Type v} (Z : Option V → Type u)
  [∀ i, TopologicalSpace (Z i)] [∀ i, ChartedSpace H (Z i)] [∀ i, IsManifold I ∞ (Z i)]

def sigmaOptionDiffeomorph : Diffeomorph I I (Σ i, Z i) (Z none ⊕ (Σ i, Z (some i))) ∞ := by
  have hf : IsLocalDiffeomorph I I ∞ (Homeomorph.sigmaOption Z) := by
    apply (isLocalDiffeomorph_sigma_iff _).mpr
    intro i
    cases i with
    | none => exact isLocalDiffeomorph_sum_inl (M := Z none) (N := Σ i, Z (some i))
    | some v =>
      change IsLocalDiffeomorph I I ∞ (Sum.inr ∘ (fun x : Z (some v) => (⟨v, x⟩ : Σ j, Z (some j))))
      exact DifferentialGeometry.isLocalDiffeomorph_comp
        (isLocalDiffeomorph_sum_inr (I := I) (M := Σ j, Z (some j)) (N := Z none))
        (isLocalDiffeomorph_sigmaMk (I := I) (M := fun j => Z (some j)) v)
  exact hf.diffeomorphOfBijective (Homeomorph.sigmaOption Z).bijective

@[simp] theorem sigmaOptionDiffeomorph_apply (x : Σ i, Z i) :
    sigmaOptionDiffeomorph (I := I) Z x = Homeomorph.sigmaOption Z x := rfl

end DifferentialGeometry.Topology
