# Source and compatibility port

Upstream: https://github.com/alonamaloh/schoenflies-lean

Revision: `05a43d29cde026618777db3d4e4316204ccca237`

Author: Álvaro Begué. Apache 2.0; original notices and LICENSE retained.
The 128-module transitive dependency closure of `Schoenflies.JordanSchoenflies`
is included. It contains the previously selected 76-module `JordanClosed`
closure. The comparator challenge is not included.

Ported from Lean 4.32.2 to Lean 4.34.0 and the parent project's Mathlib pin.
The [alignment record](ALIGNMENT.json) reports 125 identical files after
line-ending normalization, with these three proof compatibility adaptations:

- `Subarc.lean`: `image_reparam_I` explicitly unfolds the interval and
  reparametrisation before simplifying scalar multiplication.
- `Endgame.lean`: `exists_isHomeoOn_of_homeomorph` uses `Set.domRestrict`
  and the corresponding continuity and application lemmas after their rename.
- `InitialPair.lean`: `exists_isSetHomeoOn_modelCurve` has the same restriction
  rename in its continuity proof.

No theorem statements or definitions were changed. The complete selected
source closure and our Jordan-domain simple-connectivity consequence built
successfully on 17 September 2026. The parent's audit includes the public
square-extension and bundled Jordan–Schoenflies theorems. Its verification
scan and source hashes now include all 128 vendored modules.

These topological proofs remain attributed to their public author. Our
application uses closed-interior extension to prove simple connectivity;
it does not assert an extension of arbitrary conformal maps to the plane.
