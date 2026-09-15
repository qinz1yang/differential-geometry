import DifferentialGeometry.Topology.Homology.ConeTriangleNaturality
import DifferentialGeometry.Topology.Simplex.SkeletonSupportFaceGluing
import DifferentialGeometry.Topology.Simplex.SkeletonHomotopyExtension
import DifferentialGeometry.Topology.Simplex.OrderedSupportFace
import DifferentialGeometry.Topology.Homology.ConeTriangleHomotopy
import DifferentialGeometry.Topology.Simplex.SupportFace
import DifferentialGeometry.Topology.Simplex.Reindex
import Mathlib.Data.Finset.Sort

noncomputable section
namespace DifferentialGeometry.Topology
open Simplex
open CategoryTheory AlgebraicTopology
open scoped Simplicial
universe u
variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

private def supportTriangleSimplex (tau : integralSingularSimplex 4 X)
    (s : Finset (Fin 5)) (hs : s.card = 3) : integralSingularSimplex 2 X :=
  (integralSingularSimplexEquiv 2 X).symm
    ((integralSingularSimplexEquiv 4 X tau).comp
      ⟨stdSimplex.map (s.orderEmbOfFin hs), stdSimplex.continuous_map (s.orderEmbOfFin hs)⟩)

omit [SimplyConnectedSpace X] in
private theorem supportTriangleSimplex_apply (tau : integralSingularSimplex 4 X)
    (s : Finset (Fin 5)) (hs : s.card = 3) (p : stdSimplex ℝ (Fin 3)) :
    integralSingularSimplexEquiv 2 X (supportTriangleSimplex tau s hs) p =
      integralSingularSimplexEquiv 4 X tau (Simplex.orderedSupportFaceHomeomorph s hs p).val := by
  rw [supportTriangleSimplex, Equiv.apply_symm_apply]
  exact congrArg (integralSingularSimplexEquiv 4 X tau)
    (orderedSupportFaceHomeomorph_apply_val s hs p).symm

variable (x : X) [Subsingleton (HomotopyGroup (Fin 2) X x)]

private def supportTriangleConeHomotopy (tau : integralSingularSimplex 4 X)
    (s : Finset (Fin 5)) (hs : s.card = 3) : C(unitInterval × Simplex.supportFace s, X) :=
  (integralSingularConeTriangleHomotopy x (supportTriangleSimplex tau s hs)).comp
    ⟨fun z => (z.1,(Simplex.orderedSupportFaceHomeomorph s hs).symm z.2),
      continuous_fst.prodMk ((Simplex.orderedSupportFaceHomeomorph s hs).symm.continuous.comp continuous_snd)⟩

private theorem supportTriangleConeHomotopy_zero (tau : integralSingularSimplex 4 X)
    (s : Finset (Fin 5)) (hs : s.card = 3) (p : Simplex.supportFace s) :
    supportTriangleConeHomotopy x tau s hs (0,p) = integralSingularSimplexEquiv 4 X tau p.val := by
  change integralSingularConeTriangleHomotopy x (supportTriangleSimplex tau s hs)
    (0,(Simplex.orderedSupportFaceHomeomorph s hs).symm p) = _
  rw [integralSingularConeTriangleHomotopy_zero, supportTriangleSimplex_apply,
    Homeomorph.apply_symm_apply]

private theorem supportTriangleConeHomotopy_one (tau : integralSingularSimplex 4 X)
    (s : Finset (Fin 5)) (hs : s.card = 3) (p : Simplex.supportFace s) :
    supportTriangleConeHomotopy x tau s hs (1,p) = x :=
  integralSingularConeTriangleHomotopy_one x (supportTriangleSimplex tau s hs) _


private theorem supportFace_homotopy_overlap
    (tau : integralSingularSimplex 4 X)
    (s r : {s : Finset (Fin 5) // s.card = 3})
    (t : unitInterval) (p : stdSimplex ℝ (Fin 5))
    (hs : p ∈ Simplex.supportFace s.val) (hr : p ∈ Simplex.supportFace r.val) :
    supportTriangleConeHomotopy x tau s.val s.property (t,⟨p,hs⟩) =
      supportTriangleConeHomotopy x tau r.val r.property (t,⟨p,hr⟩) := by
  let es := orderedSupportFaceHomeomorph s.val s.property
  let er := orderedSupportFaceHomeomorph r.val r.property
  change integralSingularConeTriangleHomotopy x (supportTriangleSimplex tau s.val s.property)
      (t, es.symm ⟨p,hs⟩) =
    integralSingularConeTriangleHomotopy x (supportTriangleSimplex tau r.val r.property)
      (t, er.symm ⟨p,hr⟩)
  apply integralSingularConeTriangleHomotopy_comp_map_eq x
    (integralSingularSimplexEquiv 4 X tau)
    (s.val.orderEmbOfFin s.property).strictMono
    (r.val.orderEmbOfFin r.property).strictMono
  calc
    stdSimplex.map (s.val.orderEmbOfFin s.property) (es.symm ⟨p,hs⟩) = p := by
      rw [← orderedSupportFaceHomeomorph_apply_val]
      exact congrArg Subtype.val (es.apply_symm_apply ⟨p,hs⟩)
    _ = stdSimplex.map (r.val.orderEmbOfFin r.property) (er.symm ⟨p,hr⟩) := by
      rw [← orderedSupportFaceHomeomorph_apply_val]
      exact (congrArg Subtype.val (er.apply_symm_apply ⟨p,hr⟩)).symm


theorem exists_fourSimplex_cone_triangle_homotopy
    (tau : integralSingularSimplex 4 X) :
    ∃ F : C(unitInterval × stdSimplex ℝ (Fin 5), X),
      (∀ p, F (0,p) = integralSingularSimplexEquiv 4 X tau p) ∧
      (∀ (s : Finset (Fin 5)) (hs : s.card = 3) (t : unitInterval)
        (p : stdSimplex ℝ (Fin 3)),
        F (t,stdSimplex.map (s.orderEmbOfFin hs) p) =
          integralSingularConeTriangleHomotopy x
            ((integralSingularSimplexEquiv 2 X).symm
              ((integralSingularSimplexEquiv 4 X tau).comp
                ⟨stdSimplex.map (s.orderEmbOfFin hs),
                  stdSimplex.continuous_map (s.orderEmbOfFin hs)⟩)) (t,p)) ∧
      ∀ p : Simplex.skeleton (Fin 5) 2, F (1,p.val) = x := by
  let G : (s : {s : Finset (Fin 5) // s.card = 3}) →
      C(unitInterval × supportFace s.val, X) :=
    fun s => supportTriangleConeHomotopy x tau s.val s.property
  have hG : ∀ (s r : {s : Finset (Fin 5) // s.card = 3}) (t : unitInterval)
      (p : stdSimplex ℝ (Fin 5)) (hs : p ∈ supportFace s.val) (hr : p ∈ supportFace r.val),
      G s (t,⟨p,hs⟩) = G r (t,⟨p,hr⟩) := supportFace_homotopy_overlap x tau
  let H := skeletonHomotopyDesc (show 2 + 1 ≤ Fintype.card (Fin 5) by decide) G hG
  have hH : ∀ p : skeleton (Fin 5) 2,
      H (0,p) = integralSingularSimplexEquiv 4 X tau p.val :=
    skeletonHomotopyDesc_zero _ G hG (integralSingularSimplexEquiv 4 X tau)
      (fun s p => supportTriangleConeHomotopy_zero x tau s.val s.property p)
  obtain ⟨F,hF0,hFs⟩ := exists_continuous_homotopy_extension_skeleton 2
    (integralSingularSimplexEquiv 4 X tau) H hH
  refine ⟨F,hF0,?_,?_⟩
  · intro s hs t p
    let e := orderedSupportFaceHomeomorph s hs
    have h := (hFs t ⟨(e p).val, supportFace_subset_skeleton hs.le (e p).property⟩).trans
      (skeletonHomotopyDesc_supportFace _ G hG ⟨s,hs⟩ t (e p))
    change F (t,(e p).val) =
      integralSingularConeTriangleHomotopy x (supportTriangleSimplex tau s hs)
        (t,e.symm (e p)) at h
    rw [e.symm_apply_apply] at h
    rw [orderedSupportFaceHomeomorph_apply_val] at h
    exact h
  · intro p
    exact (hFs 1 p).trans (skeletonHomotopyDesc_eq _ G hG 1 (fun _ => x)
      (fun s p => supportTriangleConeHomotopy_one x tau s.val s.property p) p)

end DifferentialGeometry.Topology
