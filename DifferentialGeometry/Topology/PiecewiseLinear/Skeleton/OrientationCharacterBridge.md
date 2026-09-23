# Relative orientation character for CGN edge matching

This is a Q3 probe, not a proof or an additional hypothesis of
exists_section34EdgeMatching. The verified chart transport is
SphereHoledBoundaryExtension.lean. It accepts a PL chart of each closed complementary
surface disk, a reference disk map, and prescribed boundary maps with positive corrections.
The following producers must be derived from the frozen CGN inputs before that theorem can
close exists_joint_boundary_matching.

## Exact sub-leaves

1. exists_planar_chart_of_spherical_complement: for each vertex boundary
   srcBd (.vertexBall w) and DvBd w, use the PL 2-sphere structures supplied by
   Section34CutFrame and hDv, plus the chosen incident disk, to obtain a PL map
   from the closed complementary PL 2-disk to a full-dimensional planar PL 2-disk.
   The other incident PL disks must map to pairwise disjoint PL 2-disks in its
   ambient planar interior. Their intrinsic rim circles must map to the planar
   frontiers. The ambient frontier of a 2-disk in E3 is the entire disk, so replacing
   an intrinsic rim by frontier in E3 would be false.
2. exists_marked_sphere_reference_maps: choose the outer boundary map and a
   labelled reference disk map at every vertex, agreeing on each shared source
   splitting disk and mapping it to the fixed Dd e. The choices must be simultaneous
   across all vertices; independently chosen single-disk maps do not satisfy this.
3. relative_orientation_character_cycle_zero: let
   V = Section34VertexIndex K K',
   E = Section34EdgeIndex K K', and ends : E -> V x V.
   From the source and target marked sphere charts, define edge signs
   sourceSign, targetSign : E -> ZMod 2 as the orientation changes across each
   shared disk, with the boundary-normal reversal included. For every mod-two
   edge cycle F : Finset E (each vertex has even incidence in F), prove
   sum_{e in F} (sourceSign e + targetSign e) = 0.
   This equality must be obtained from the original embedding h and the
   fixed hframe/hprep/hpack geometry. The absolute source or target character
   need not vanish: the ambient manifolds have no global orientability hypothesis.
4. exists_vertex_signs_of_cycle_zero: for a finite graph with endpoints ends
   and relativeSign e = sourceSign e + targetSign e, prove that the preceding
   cycle condition yields sigma : V -> ZMod 2 with
   relativeSign e = sigma (ends e).1 + sigma (ends e).2 for every edge.
   This is the graph coboundary lemma; loops and parallel edges must be covered.
5. positive_boundary_corrections_of_vertex_signs: adjust each chosen vertex
   reference chart by sigma w, then prove the coordinate correction for every
   prescribed rim map satisfies the exact IsPLCirclePositive predicate used by
   HoledDiskBoundaryExtension. The same disk map must be consumed at both
   endpoints of an edge.
6. exists_joint_boundary_matching_of_orientation_character: assemble the
   preceding outputs with SphereHoledBoundaryExtension, then extend each full
   matched boundary sphere over its vertex PL 3-cell by the already checked
   exists_extension_of_cell_boundary. The output must retain all four map and
   overlap equations in exists_joint_boundary_matching.

The graph-cycle equality in item 3 is an output to prove, never an added
hypothesis at the frozen endpoint. Item 4 is independent finite-graph algebra.
The chart-transport module establishes the final local extension once items
1, 2, and 5 supply its actual inputs. No Opus-owned leaf or frozen statement
was edited for this probe.
