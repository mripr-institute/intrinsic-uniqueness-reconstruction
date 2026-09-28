# F5 tensor-square bridge proof record

Target: the tensor-square component of `final:F5` in
`paper/sections/series-realizations.tex`. This is a component proof, not a
claim that the entire proposition is formalized.

## Verified construction

`SigmaRealProjectiveSquareTriviality.lean` constructs the actual algebraic
tensor square of each complexified tautological fiber and identifies it
linearly with the concrete incidence line in `RP² × ℂ⁹`. The map on a pure
tensor has coordinates `x i * y j`.

`SigmaRealProjectiveSquareNativeBundle.lean` constructs the bundle with the
squared coordinate cocycle from `SigmaRealProjectiveSquareTransition.lean`
and proves a total-space homeomorphism to the
concrete tensor-square incidence space. The homeomorphism preserves the
projective base and is complex-linear on every fiber. It also gives the
family of algebraic tensor-square fibers the topology induced by the
canonical tensor-coordinate embedding into that incidence space, then
identifies this topologized family with the squared-cocycle bundle. The
pure-tensor coordinate formula is proved explicitly.

`SigmaRealProjectiveSquareNativeTensor.lean` registers the family of actual
tensor-product fibers as a native Mathlib `FiberBundle` and `VectorBundle` of
rank one. Its global trivialization is a native `Trivialization`; the public
homeomorphism preserves the base and is complex-linear on each fiber.

`SigmaRealProjectiveF5Characteristic.lean` proves unconditionally that the
complexified line and this tensor-square bundle are not isomorphic over the
fixed base. It also proves the rational-ring calculation and assembles the
fixed-base rational-characteristic witness under three explicit inputs:
the line's K-class squares to one, its reduced rational Chern character has
square zero, and the tensor-square bundle has Chern character one. These
inputs are not proved by the current topology and supplied-theory APIs.
The algebraic determinant-cancellation step is isolated as
`not_stably_equivalent_of_cancellative_invariant`; its application still
requires an actual additive determinant invariant on native bundle classes.

Key declarations:

- `Sigma.realProjectiveSquaredCocycleIncidenceHomeomorph`
- `Sigma.real_projective_squared_cocycle_incidence_fiberwise_linear`
- `Sigma.real_projective_complex_tensor_square_to_incidence_tmul`
- `Sigma.realProjectiveSquaredCocycleTensorSquareHomeomorph`
- `Sigma.real_projective_squared_cocycle_tensor_square_projection`
- `Sigma.real_projective_squared_cocycle_tensor_square_fiberwise_linear`
- `Sigma.realProjectiveComplexTensorSquareTotalTrivialization`
- `Sigma.real_projective_complex_tensor_square_total_trivialization_fiberwise_linear`
- `Sigma.realProjectiveComplexTensorSquareNativeBundle`
- `Sigma.realProjectiveComplexTensorSquareFinOneHomeomorph`
- `Sigma.real_projective_complex_tensor_square_native_trivialization_fiberwise_linear`
- `Sigma.real_projective_complex_line_not_isomorphic_tensor_square`
- `Sigma.real_projective_chern_character_of_square_and_reduced_square_zero`
- `Sigma.real_projective_fixed_base_rational_characteristic_witness_of_inputs`

The topology here is explicitly constructed from the concrete tensor
coordinates. The native bundle structure is built directly for this
rank-one family. This record does not claim an equivalence to a separately
defined general-purpose tensor-product bundle topology.

## Verification and remaining scope

The targeted `SigmaRealProjectiveSquareNativeBundle` build, complete `Sigma`
import-graph build, and source audit pass with the pinned Lean toolchain.
The long `SigmaAxioms.lean` audit was not run for this revision. No
independent formal audit has yet reviewed this component, so the current
coverage ledger remains unchanged.

The stable complex `K⁰` distinction (including determinant cancellation) and
the actual RP² rational cohomology/Chern-character inputs remain open in
Lean. The fixed-base witness is proved for native bundle isomorphism, while
its rational-characteristic version is conditional on those missing inputs.
`final:F5` remains partial.
