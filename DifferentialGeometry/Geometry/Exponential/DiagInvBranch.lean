import DifferentialGeometry.Geometry.Exponential.ExpVariationSmooth
import DifferentialGeometry.Geometry.Exponential.ExpInvBranch
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic

set_option autoImplicit false

/-!
# Selected inverse branches for the diagonal exponential

This file defines the branch object shared by the generic diagonal-exponential
inverse and quantitative consumers.  The object records one explicit local
inverse branch; quantitative source and target radii belong to the producer
that selects a branch, not to this generic interface.
-/

noncomputable section

open Bundle Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- A selected smooth local inverse branch of the intrinsic diagonal
exponential at the zero tangent vector over `p`.

The branch carries no quantitative radius: such bounds belong to the theorem
that selects a branch for a particular geometric application. -/
structure DiagInvBranch
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) where
  hom : OpenPartialHomeomorph (TangentBundle I M) (M × M)
  zero_mem :
    (⟨p, (0 : TangentSpace I p)⟩ : TangentBundle I M) ∈ hom.source
  hom_eq : EqOn (fun u ↦ hom u) (diagExp (I := I) g hEnorm) hom.source
  inv_inf : ContMDiffOn (I.prod I) I.tangent ∞ hom.symm hom.target

namespace DiagInvBranch

/-- The totalized inverse function selected by a diagonal-exponential branch. -/
def inv
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p) :
    M × M → TangentBundle I M :=
  B.hom.symm

/-- The target domain on which the selected inverse laws hold. -/
def dom
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p) : Set (M × M) :=
  B.hom.target

/-- The selected branch is a right inverse of `diagExp` on its target. -/
theorem right_inv
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p)
    {y : M × M} (hy : y ∈ B.dom) :
    diagExp (I := I) g hEnorm (B.inv y) = y := by
  have hu : B.inv y ∈ B.hom.source := B.hom.map_target hy
  calc
    diagExp (I := I) g hEnorm (B.inv y) = B.hom (B.inv y) :=
      (B.hom_eq hu).symm
    _ = y := by simpa only [inv] using B.hom.right_inv hy

/-- The selected branch is a left inverse of `diagExp` on its source. -/
theorem left_inv
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p)
    {u : TangentBundle I M} (hu : u ∈ B.hom.source) :
    B.inv (diagExp (I := I) g hEnorm u) = u := by
  calc
    B.inv (diagExp (I := I) g hEnorm u) = B.inv (B.hom u) :=
      congrArg B.inv (B.hom_eq hu).symm
    _ = u := by simpa only [inv] using B.hom.left_inv hu

/-- A tangent vector in the selected source is recovered from its intrinsic
exponential endpoint by the selected inverse. -/
theorem inv_eq_of_exp
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p y pt : M} (B : DiagInvBranch (I := I) g hEnorm p)
    {v : TangentSpace I y}
    (hvsrc : (⟨y, v⟩ : TangentBundle I M) ∈ B.hom.source)
    (hexp : expMapIntrinsic (I := I) g hEnorm y v = pt) :
    B.inv (y, pt) = (⟨y, v⟩ : TangentBundle I M) := by
  have hdiag :
      diagExp (I := I) g hEnorm (⟨y, v⟩ : TangentBundle I M) = (y, pt) := by
    change (y, expMapIntrinsic (I := I) g hEnorm y v) = (y, pt)
    rw [hexp]
  rw [← hdiag]
  exact B.left_inv hvsrc

/-- On the selected inverse domain, the inverse tangent vector is based at the
first point of the pair. -/
theorem proj_eq
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p)
    {y : M × M} (hy : y ∈ B.dom) :
    (B.inv y).proj = y.1 := by
  simpa only [diagExp_fst] using congrArg Prod.fst (B.right_inv hy)

/-- Fixing the endpoint of a selected inverse branch gives a smooth tangent
section wherever the corresponding pairs stay in the branch domain. -/
theorem inv_snd_inf
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖₊ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p pt : M} (B : DiagInvBranch (I := I) g hEnorm p) {S : Set M}
    (hdom : ∀ y ∈ S, (y, pt) ∈ B.dom) :
    ContMDiffOn I I.tangent ∞
      (T% fun y => show TangentSpace I y from (B.inv (y, pt)).snd) S := by
  have hpair : ContMDiffOn I (I.prod I) ∞ (fun y : M ↦ (y, pt)) S :=
    (contMDiff_id.prodMk contMDiff_const).contMDiffOn
  have hinv : ContMDiffOn I I.tangent ∞
      (fun y : M ↦ B.inv (y, pt)) S := by
    simpa only [inv, dom, Function.comp_apply] using B.inv_inf.comp hpair hdom
  refine hinv.congr ?_
  intro y hy
  refine TotalSpace.ext (B.proj_eq (hdom y hy)).symm ?_
  exact heq_of_eq rfl

/-- Fixing the first point of a selected inverse branch gives a smooth
tangent-bundle map wherever the corresponding pairs stay in the branch
domain. -/
theorem inv_fst_inf
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p pt : M} (B : DiagInvBranch (I := I) g hEnorm p) {S : Set M}
    (hdom : ∀ y ∈ S, (pt, y) ∈ B.dom) :
    ContMDiffOn I I.tangent ∞ (fun y : M ↦ B.inv (pt, y)) S := by
  have hpair : ContMDiffOn I (I.prod I) ∞ (fun y : M ↦ (pt, y)) S :=
    (contMDiff_const.prodMk contMDiff_id).contMDiffOn
  simpa only [inv, dom, Function.comp_apply] using B.inv_inf.comp hpair hdom

/-- Fixing the first point of a selected inverse branch gives a smooth
model-coordinate inverse vector on every set contained in the branch domain.

This is the fixed-fiber companion of `inv_fst_inf`.  It uses the canonical
tangent-bundle trivialization at the fixed point and hides that representation
choice from downstream inverse-derivative arguments. -/
theorem inv_fst_coord_inf
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {c p : M} (B : DiagInvBranch (I := I) g hEnorm c) {S : Set M}
    (hdom : ∀ z ∈ S, (p, z) ∈ B.dom) :
    ContMDiffOn I 𝓘(Real, E) ∞
      (fun z : M => ((B.inv (p, z)).snd : E)) S := by
  have hinv : ContMDiffOn I I.tangent ∞
      (fun z : M => B.inv (p, z)) S :=
    B.inv_fst_inf hdom
  have hmaps :
      MapsTo (fun z : M => B.inv (p, z)) S
        (Geodesic.geodesicChartDomain (I := I) p) := by
    intro z hz
    apply Geodesic.mem_geodesicChartDomain_of_proj
    rw [B.proj_eq (hdom z hz)]
    exact mem_chart_source H p
  have hcoord : ContMDiffOn I 𝓘(Real, E) ∞
      (fun z : M => Geodesic.chartFiberCoord (I := I) p (B.inv (p, z))) S :=
    (Geodesic.chartFiberCoord_contMDiffOn (I := I) p).comp hinv hmaps
  refine hcoord.congr ?_
  intro z hz
  have hproj : (B.inv (p, z)).proj = p := B.proj_eq (hdom z hz)
  have htotal :
      B.inv (p, z) =
        (⟨p, (show TangentSpace I p from (B.inv (p, z)).snd)⟩ :
          TangentBundle I M) := by
    apply TotalSpace.ext hproj
    exact heq_of_eq rfl
  rw [htotal]
  exact (Geodesic.chartFiberCoord_mk_self (I := I) p
    (show TangentSpace I p from (B.inv (p, z)).snd)).symm

/-- On the selected inverse domain, exponentiating its fiber component gives
the second point of the pair. -/
theorem exp_eq
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p)
    {y : M × M} (hy : y ∈ B.dom) :
    expMapIntrinsic (I := I) g hEnorm y.1 (B.inv y).snd = y.2 := by
  have h :
      expMapIntrinsic (I := I) g hEnorm (B.inv y).proj (B.inv y).snd = y.2 := by
    have hright := congrArg Prod.snd (B.right_inv hy)
    change
      expMapIntrinsic (I := I) g hEnorm (B.inv y).proj (B.inv y).snd = y.2 at hright
    exact hright
  rwa [B.proj_eq hy] at h

/-- Fixing the first point of a diagonal inverse branch gives the canonical
fixed-first intrinsic-exponential branch. -/
noncomputable def fixed
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {c : M} (B : DiagInvBranch (I := I) g hEnorm c) (p : M) :
    ExpInvBranch (I := I) g hEnorm p := by
  classical
  let e := trivializationAt E (TangentSpace I) p
  have hp : p ∈ e.baseSet := by
    change p ∈ (trivializationAt E (TangentSpace I) p).baseSet
    rw [TangentBundle.trivializationAt_baseSet]
    exact mem_chart_source H p
  have hpair : ContMDiff 𝓘(Real, E) (I.prod 𝓘(Real, E)) ∞
      (fun v : E => (p, v)) :=
    contMDiff_const.prodMk contMDiff_id
  have hmaps : ∀ v : E, (p, v) ∈ e.target := by
    intro v
    rw [Bundle.Trivialization.target_eq]
    exact ⟨hp, Set.mem_univ _⟩
  have hsymm : ContMDiff 𝓘(Real, E) I.tangent ∞
      (fun v : E => e.toOpenPartialHomeomorph.symm (p, v)) := by
    apply contMDiffOn_univ.mp
    exact e.contMDiffOn_symm.comp hpair.contMDiffOn
      (fun v _ => hmaps v)
  have heq : (fun v : E => e.toOpenPartialHomeomorph.symm (p, v)) =
      (fun v : E => (⟨p, v⟩ : TangentBundle I M)) := by
    funext v
    have hsrc : (⟨p, v⟩ : TangentBundle I M) ∈ e.source := by
      rw [e.mem_source]
      exact hp
    have heval :
        e.toOpenPartialHomeomorph (⟨p, v⟩ : TangentBundle I M) = (p, v) := by
      apply Prod.ext
      · rfl
      · exact Geodesic.chartFiberCoord_mk_self (I := I) p v
    rw [← heval]
    exact e.left_inv hsrc
  have hfiber : ContMDiff 𝓘(Real, E) I.tangent ∞
      (fun v : E => (⟨p, v⟩ : TangentBundle I M)) := by
    rw [← heq]
    exact hsymm
  let Φ : PartialDiffeomorph 𝓘(Real, E) I E M ∞ :=
    { toFun := fun u : E =>
        expMapIntrinsic (I := I) g hEnorm p
          (show TangentSpace I p from u)
      invFun := fun y : M => ((B.inv (p, y)).snd : E)
      source :=
        {u : E | (⟨p, show TangentSpace I p from u⟩ :
          TangentBundle I M) ∈ B.hom.source}
      target := {y : M | (p, y) ∈ B.dom}
      map_source' := by
        intro u hu
        have hmap := B.hom.map_source hu
        have hEq :
            B.hom
                (⟨p, show TangentSpace I p from u⟩ :
                  TangentBundle I M) =
              (p, expMapIntrinsic (I := I) g hEnorm p
                (show TangentSpace I p from u)) := by
          simpa only [diagExp] using B.hom_eq hu
        have hpair :
            (p, expMapIntrinsic (I := I) g hEnorm p
              (show TangentSpace I p from u)) ∈ B.hom.target :=
          hEq ▸ hmap
        exact hpair
      map_target' := by
        intro y hy
        have hsrc : B.inv (p, y) ∈ B.hom.source :=
          B.hom.map_target hy
        have htotal :
            B.inv (p, y) =
              (⟨p, show TangentSpace I p from (B.inv (p, y)).snd⟩ :
                TangentBundle I M) := by
          apply TotalSpace.ext (B.proj_eq hy)
          exact heq_of_eq rfl
        change
          (⟨p, show TangentSpace I p from (B.inv (p, y)).snd⟩ :
            TangentBundle I M) ∈ B.hom.source
        rw [← htotal]
        exact hsrc
      left_inv' := by
        intro u hu
        have hleft := B.left_inv hu
        have hdiag :
            diagExp (I := I) g hEnorm
                (⟨p, show TangentSpace I p from u⟩ : TangentBundle I M) =
              (p, expMapIntrinsic (I := I) g hEnorm p
                (show TangentSpace I p from u)) := by
          rfl
        rw [hdiag] at hleft
        exact congrArg (fun z : TangentBundle I M => (z.snd : E)) hleft
      right_inv' := by
        intro y hy
        exact B.exp_eq hy
      open_source := B.hom.open_source.preimage hfiber.continuous
      open_target :=
        B.hom.open_target.preimage (continuous_const.prodMk continuous_id)
      contMDiffOn_toFun :=
        (intrinsicFiber_smooth (I := I) g hEnorm p).contMDiffOn
      contMDiffOn_invFun :=
        B.inv_fst_coord_inf (S := {y : M | (p, y) ∈ B.dom})
          (fun y hy => hy) }
  exact ⟨Φ, fun _ _ => rfl⟩

/-- Membership in the fixed branch source is membership of the corresponding
tangent-bundle vector in the diagonal branch source. -/
@[simp] theorem fixed_source
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {c p : M} (B : DiagInvBranch (I := I) g hEnorm c) (u : E) :
    u ∈ (B.fixed p).hom.source ↔
      (⟨p, show TangentSpace I p from u⟩ : TangentBundle I M) ∈
        B.hom.source :=
  Iff.rfl

/-- Membership in the fixed branch target is membership of the corresponding
pair in the diagonal branch target. -/
@[simp] theorem fixed_target
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {c p : M} (B : DiagInvBranch (I := I) g hEnorm c) (y : M) :
    y ∈ (B.fixed p).dom ↔ (p, y) ∈ B.dom :=
  Iff.rfl

/-- Inside the named realized-exponential radius, a selected branch inverse is
the moving normal-coordinate inverse. -/
theorem inv_eq_normal_lt
    [T2Space (TangentBundle I M)]
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p y q : M} (B : DiagInvBranch (I := I) g hEnorm p)
    (hy : (y, q) ∈ B.dom)
    (hsmall : Real.sqrt
      (g.inner y (B.inv (y, q)).snd (B.inv (y, q)).snd) <
        expDiffeoRadius (I := I) g hEnorm y) :
    B.inv (y, q) =
      (⟨y, (show TangentSpace I y from
        NormalCoordinates.normalChartAt (I := I) g y q)⟩ : TangentBundle I M) := by
  have hsrc := expDiffeo_mem_of_lt (I := I) g hEnorm y hsmall
  have hcompat := expDiffeo_eq_intr (I := I) g hEnorm y hsmall
  have hexp : NormalCoordinates.expMapDiffeo (I := I) g y
      (show TangentSpace I y from (B.inv (y, q)).snd) = q :=
    hcompat.trans (B.exp_eq hy)
  have hcoord : (NormalCoordinates.normalChartAt (I := I) g y q : E) =
      (B.inv (y, q)).snd := by
    have hleft := (NormalCoordinates.expMapDiffeo (I := I) g y).left_inv hsrc
    rw [hexp] at hleft
    exact hleft
  refine TotalSpace.ext (B.proj_eq hy) ?_
  exact heq_of_eq hcoord.symm

/-- The diagonal pair belongs to the target domain of every selected branch. -/
theorem center_mem
    [T2Space (TangentBundle I M)]
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p) :
    (p, p) ∈ B.dom := by
  let z : TangentBundle I M := ⟨p, (0 : TangentSpace I p)⟩
  have hz : z ∈ B.hom.source := B.zero_mem
  have hmap : B.hom z ∈ B.hom.target := B.hom.map_source hz
  have heq : B.hom z = diagExp (I := I) g hEnorm z := by
    simpa only using B.hom_eq hz
  have hdiag : diagExp (I := I) g hEnorm z = (p, p) := by
    apply Prod.ext
    · rfl
    · exact expMapIntrinsic_zero (I := I) g hEnorm p
  rw [heq, hdiag] at hmap
  exact hmap

/-- The selected inverse sends the diagonal pair to the zero tangent vector. -/
theorem center_inv
    [T2Space (TangentBundle I M)]
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p) :
    B.inv (p, p) =
      (⟨p, (0 : TangentSpace I p)⟩ : TangentBundle I M) := by
  let z : TangentBundle I M := ⟨p, (0 : TangentSpace I p)⟩
  have hz : z ∈ B.hom.source := B.zero_mem
  have hleft := B.left_inv hz
  have hdiag : diagExp (I := I) g hEnorm z = (p, p) := by
    apply Prod.ext
    · rfl
    · exact expMapIntrinsic_zero (I := I) g hEnorm p
  rw [hdiag] at hleft
  exact hleft

end DiagInvBranch
end Exponential
end Riemannian
end Geometry
end DifferentialGeometry
