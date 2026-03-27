# Kepler's Laws via Comoment Maps in Lean 4

This repository formalizes Kepler's laws in Lean 4 using the comoment map approach.
The main mathematical reference is Victor Guillemin and Shlomo Sternberg, *Variations on a Theme by Kepler* (AMS Colloquium Publications, Vol. 42).

## Structure

The development is split across five Lean files.

1. `Kepler/Definitions.lean`
   Basic objects: phase space, energy, angular momentum, and the Laplace--Runge--Lenz vector.
2. `Kepler/Dynamics.lean`
   The Kepler vector field and the notion of a non-collision solution.
3. `Kepler/ConservedQuantities.lean`
   Conservation of angular momentum, energy, and the Laplace--Runge--Lenz vector.
4. `Kepler/MomentMap.lean`
   The Poisson bracket, rotational observables, and the hidden `so(4)` structure on negative-energy shells.
5. `Kepler/KeplerLaws.lean`
   Orbit geometry, Kepler's three laws, and the final synthesis theorem.

## Key Definitions

- `MassParam`, `GravitationalParam`
- `PhaseSpace`
- `energy`
- `angularMomentum`
- `laplaceLenz`
- `IsSolution`

## Key Theorems

- `angularMomentum_const`
- `energy_const`
- `laplaceLenz_const`
- `rotational_comoment`
- `hidden_so4_comoment`
- `kepler_first_law_source`
- `kepler_second_law_source`
- `kepler_third_law`
- `kepler_laws_from_comoment`

## Blueprint

The repository includes a `leanblueprint` blueprint in `blueprint/`.
It gives the chapter-by-chapter structure of the formal proof and links the main statements to the Lean declarations.

## Building the Project

To build the project, run the following command:

```bash
lake build
```

## Dependencies

This project depends on Lean 4 and Mathlib.

## References

- Victor Guillemin and Shlomo Sternberg, *Variations on a Theme by Kepler*, Colloquium Publications 42, American Mathematical Society, 1990.
- AMS page: <https://bookstore.ams.org/COLL/42>

## License

This project is licensed under the MIT License.
