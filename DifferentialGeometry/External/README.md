# External

Third-party libraries vendored into this project.

## `Schoenflies/`

- **Source**: https://github.com/alonamaloh/schoenflies-lean
- **Commit**: `05a43d29cde026618777db3d4e4316204ccca237`
- **Author**: Álvaro Begué
- **License**: Apache-2.0 (`Schoenflies/LICENSE`)

The planar Jordan--Schoenflies theorem and its transitive dependencies.
See `Schoenflies/PORTING.md` for scope and validation, and
`Schoenflies/MODIFICATIONS.md` for local changes. Original attribution and
documentation are preserved.

## `DeGiorgi/`

- **Source**: https://github.com/scottnarmstrong/DeGiorgi
- **Commit**: `4c1b307`
- **Authors**: Scott Armstrong, Julia Kempe
- **Paper**: arXiv:2604.05984
- **License**: Apache-2.0 (`DeGiorgi/LICENSE`)

Original `LICENSE`, `README.md`, and `CITATION.cff` are preserved unmodified.
Any modifications we make are tracked in `DeGiorgi/MODIFICATIONS.md` per
Apache-2.0 §4(b).

## `ClassificationOfSurfaces/`

- **Source**: https://github.com/mccorvie/classification-of-surfaces
- **Commit**: `e3c7230fe78d7b056a415d9ecae6f77887046b32`
- **Authors**: ClassificationOfSurfaces contributors
- **License**: Apache-2.0 (`ClassificationOfSurfaces/LICENSE`)

Selected finite planar mesh, line-subdivision, free-triangle and geometric
attachment modules, plus the bridge to the existing native PrePolygon API.
The original namespace, README, attribution and documentation are retained.
See `ClassificationOfSurfaces/PORTING.md`, `MODIFICATIONS.md` and `UPSTREAM.patch`
for scope, exact changes and verification. This port does not include the
upstream surface-classification or polygonal Jordan development.
