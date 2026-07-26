# TowerRegularity

`iterRmComp_smoothAt` is the pure recursive regularity engine for the moving
curvature component tower.  Once the level-zero curvature components and the
Christoffel components are jointly smooth in a fixed smooth local frame, every
level produced by `iteratedRmComp` is jointly smooth.

Status: focused verification passed. This is a pure recursive engine; it does
not produce its level-zero or Christoffel regularity inputs and does not prove a
mixed time/space derivative swap.
